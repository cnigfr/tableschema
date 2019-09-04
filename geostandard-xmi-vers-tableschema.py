# -*- coding: utf-8 -*-
"""
Created on Mon May 20 16:41:00 2019

@author: richard.mitanchey
"""

from lxml import etree
import regex as re
import unicodedata
import io
import networkx as nx
from collections import OrderedDict
import json

many = re.compile(r'\.\.\*')

parser = etree.XMLParser()

nsmap = {
       "uml":"http://www.omg.org/spec/UML/20110701",
       "xmi":"http://www.omg.org/spec/XMI/20110701",
       "thecustomprofile":"http://www.sparxsystems.com/profiles/thecustomprofile/1.0",
       "UML_Profile_for_INSPIRE_data_specifications":
           "http://www.sparxsystems.com/profiles/UML_Profile_for_INSPIRE_data_specifications/3.0-2"
       }

def get_value(node, xpath):
    try:
        return node.xpath(xpath)[0]
    except:
        return ""
    
def get_model(root):
    model = {}
    for packaged_element in root.findall('.//packagedElement'):
        package_id = packaged_element.get('{http://schema.omg.org/spec/XMI/2.1}id')
        if package_id[:5] != 'EAID_':
            continue
        package_type = packaged_element.get('{http://schema.omg.org/spec/XMI/2.1}type')
        package_name = packaged_element.get('name')
        package_dict = { 'name': package_name, 'type': package_type }
        # pour les clés étrangères, on a besoin de plus de données dans le modèle
        if package_type == 'uml:Association': 
            owned_end = packaged_element.find('.//ownedEnd')
            try:
                owned_end_type = owned_end.get('{http://schema.omg.org/spec/XMI/2.1}type')
                if owned_end_type == 'uml:Property':
                    owned_end_name = owned_end.get('name')
                    package_dict['property'] = owned_end_name
            except AttributeError:
                pass
        model[package_id] = package_dict
    for owned_attribute in root.findall('.//ownedAttribute'):
        owned_attribute_id = owned_attribute.get('{http://schema.omg.org/spec/XMI/2.1}id')
        if owned_attribute_id[:5] != 'EAID_':
            continue
        packaged_element = owned_attribute.getparent()
        packaged_element_id = packaged_element.get('{http://schema.omg.org/spec/XMI/2.1}id')
        owned_attribute_type = owned_attribute.get('{http://schema.omg.org/spec/XMI/2.1}type')
        owned_attribute_name = owned_attribute.get('name')
        owned_attribute_dict = { 
                'name': owned_attribute_name, 
                'type': owned_attribute_type, 
                'parent': packaged_element_id
                }
        model[owned_attribute_id] = owned_attribute_dict
    for owned_operation in root.findall('.//ownedOperation'):
        owned_operation_id = owned_operation.get('{http://schema.omg.org/spec/XMI/2.1}id')
        if owned_operation_id[:5] != 'EAID_':
            continue
        packaged_element = owned_operation.getparent()
        packaged_element_id = packaged_element.get('{http://schema.omg.org/spec/XMI/2.1}id')
        owned_operation_type = 'ownedOperation'
        owned_operation_name = owned_operation.get('name')
        owned_operation_dict = { 
                'name': owned_operation_name, 
                'type': owned_operation_type
                }
        parameters = []
        for owned_parameter in owned_operation.findall('.//ownedParameter'):
            owned_parameter_id = owned_parameter.get('{http://schema.omg.org/spec/XMI/2.1}id')
            if owned_parameter_id[:5] != 'EAID_':
                continue
            owned_parameter_type = 'ownedParameter'
            owned_parameter_name = owned_parameter.get('name')
            parameter_dict = { 
                    'name': owned_parameter_name, 
                    'type': owned_parameter_type, 
                    'operation': owned_operation_id, 
                    'parent': packaged_element_id
                    }
            model[owned_parameter_id] = parameter_dict
            parameters.append(owned_parameter_id)
        if len(parameters)>0:
            owned_operation_dict['parameters'] = parameters
        model[owned_operation_id] = owned_operation_dict
    return model
    
def get_tableschema_name(nomtable):
    if nomtable[:2] == 'N_':
        nomtable = nomtable[2:]
    if nomtable[-4:] == '_ddd':
        nomtable = nomtable[:-4]
    return nomtable.upper()

def get_field(field_elt, codifications):
    ""
    field = {}
    field_name = field_elt.get('name')
    containment_elt = field_elt.find('.//containment')
    position = int(containment_elt.get('position'))-1
    documentation_elt = field_elt.find('.//documentation')
    documentation = documentation_elt.get('value')
    properties_elt = field_elt.find('.//properties')
    field_type = properties_elt.get('type')
    field_length = properties_elt.get('length')
    duplicates = properties_elt.get('duplicates')
    field['name'] = field_name
    if documentation:
        field['description'] = documentation
    constraints = {}
    for tag in field_elt.iterfind('.//tags/tag'):
        tag_name = tag.get('name')
        tag_value = tag.get('value')
        if tag_name == 'codification':
            enumeration = []
            codification_list = codifications[tag_value]
            for enum_dict in codification_list:
                enumeration.append(enum_dict['code'])
            constraints['enum'] = enumeration
        elif tag_name == 'pattern':
            constraints['pattern'] = tag_value
    if duplicates == '1':
        constraints['required'] = True
    if len(constraints.keys())>0:
        field['constraints'] = constraints
    return position, field

def get_primary_key(operations, model):
    ""
    primaryKeyFields = []
    for operation in operations.iterfind('.//operation'):
        stereotype_elt = operation.find('.//stereotype')
        stereotype = stereotype_elt.get('stereotype')
        if stereotype == 'PK':
            for parameter in operation.iterfind('./parameters/parameter'):
                parameter_idref = parameter.get('{http://schema.omg.org/spec/XMI/2.1}idref')
                if 'RETURNID' in parameter_idref:
                    continue
                owned_attribute = model[parameter_idref]
                PK_field = owned_attribute['name']
            primaryKeyFields.append('{}'.format(PK_field))
    if len(primaryKeyFields)==0:
        return None
    elif len(primaryKeyFields)==1:
        return primaryKeyFields[0]
    return primaryKeyFields

def get_foreign_keys(operations, links, connectors, model):
    ""
    foreignKeys = []
    for operation in operations.iterfind('.//operation'):
        operation_idref = operation.get('{http://schema.omg.org/spec/XMI/2.1}idref')
        operation_dict = model[operation_idref]
        stereotype_elt = operation.find('.//stereotype')
        stereotype = stereotype_elt.get('stereotype')
        if stereotype == 'FK':
            for parameter in operation.iterfind('./parameters/parameter'):
                parameter_idref = parameter.get('{http://schema.omg.org/spec/XMI/2.1}idref')
                if 'RETURNID' in parameter_idref:
                    continue
                owned_attribute = model[parameter_idref]
                FK_field = owned_attribute['name']
                parent_id = owned_attribute['parent']
                # pour retrouver le nom de la table destination
                # on parcourt les objets Association
                for association in links.iterfind('.//Association'):
                    association_id = association.get('{http://schema.omg.org/spec/XMI/2.1}id')
                    start_id = association.get('start')
                    end_id = association.get('end')
                    destination_id = end_id
                    if (start_id != parent_id) and (end_id == parent_id):
                        destination_id = start_id
                    # il faut alors rechercher dans le modèle le packagedElement correspondant à association_id
                    packaged_element = model[association_id]
                    if 'property' not in packaged_element.keys():
                        continue
                    if packaged_element['property'] != operation.get('name'):
                        continue
                    destination = model[destination_id]
                    destination_name = get_tableschema_name(destination['name'])
                    aForeignKey = {}
                    aForeignKey['fields'] = FK_field
                    # cas particulier d'une relation de la table vers elle-même 
                    # par convention tableschema, destination_name = ""
                    xpath_expr = './/connector[@{http://schema.omg.org/spec/XMI/2.1}idref' + '="{}"]/target/role'.format(association_id)
                    target_role_elt = connectors.find(xpath_expr)
                    target_role_name = target_role_elt.get('name')

                    if destination_id == parent_id:
                        destination_name = ""
                    destination_fields = None
                    owned_parameters = operation_dict['parameters']
                    if len(owned_parameters)==1:
                        destination_fields = model[owned_parameters[0]]['name']
                    elif len(owned_parameters)>1:
                        destination_fields = []
                        for owned_parameter in owned_parameters:
                            destination_fields.append(model[owned_parameter]['name'])
                    aForeignKey['reference'] = { 
                            'resource': destination_name, 
                            'fields': destination_fields
                            }
                    foreignKeys.append(aForeignKey)
                    break
    if len(foreignKeys)==0:
        return None
    elif len(foreignKeys)==1:
        return foreignKeys[0]
    return foreignKeys

def get_resource(element, connectors, model, codifications):
    resource = OrderedDict()
    element_type = element.get('{http://schema.omg.org/spec/XMI/2.1}type')
    if element_type.__str__() not in ['uml:Class']:
        return {}
    tablename = element.get('name')
    tableschema_name = get_tableschema_name(tablename)
    properties_elt = element.find('.//properties')
    documentation = properties_elt.get('documentation')
    operations = element.find('.//operations')
    links = element.find('.//links')
    primaryKey = get_primary_key(operations, model)
    foreignKeys = get_foreign_keys(operations, links, connectors, model)
    schema = {}
    fields = []
    fieldno = 0
    for field_elt in element.iterfind('.//attributes/attribute'):
        pos, field = get_field(field_elt, codifications)
        if len(field.keys()) > 0:
            fields.append(field)
            fieldno += 1
    #prise en compte de la géométrie
    geom_field = None
    if tableschema_name[-2:] == '_S':
        geom_field = {}
        geom_field['name'] = 'geometrie'
        geom_field['description'] = 'géométrie surfacique'
        geom_field['type'] = 'geojson'
    elif tableschema_name[-2:] == '_L':
        geom_field = {}
        geom_field['name'] = 'geometrie'
        geom_field['description'] = 'géométrie linéaire'
        geom_field['type'] = 'geojson'
    elif tableschema_name[-2:] == '_P':
        geom_field = {}
        geom_field['name'] = 'geometrie'
        geom_field['description'] = 'géométrie ponctuelle'
        geom_field['type'] = 'geojson'
    if geom_field:
        fields.append(geom_field)
        fieldno += 1
    schema['fields'] = fields
    if primaryKey:
        schema['primaryKey'] = primaryKey
    if foreignKeys:
        schema['foreignKeys'] = foreignKeys
    resource['name'] = tableschema_name
    if documentation:
        resource['description'] = documentation
    resource['schema'] = schema
    return resource

def get_codifications(tree, nsmap=nsmap):
    codifications = {}
    for element in tree.findall('.//elements/element'):
        element_name = element.get('name')
        element_type = element.get('{http://schema.omg.org/spec/XMI/2.1}type')
        if element_type == "uml:Enumeration":
            codifications[element_name] = {}
            attributes = []
            for attribute_elt in element.findall('.//attributes/attribute'):
                attribute_libelle = attribute_elt.get('name')
                initial_elt = attribute_elt.find('.//initial')
                attribute_code = initial_elt.get('body')
                attribute_dict = {}
                attribute_dict['code'] = attribute_code
                attribute_dict['libelle'] = attribute_libelle
                attributes.append(attribute_dict)
            codifications[element_name] = attributes
        elif element_type == "uml:Class":
            properties_elt = element.find('.//properties')
            stereotype = properties_elt.get('stereotype')
            if stereotype == "codeList":
                attributes = []
                for attribute_elt in element.findall('.//attributes/attribute'):
                    attribute_libelle = attribute_elt.get('name')
                    initial_elt = attribute_elt.find('.//initial')
                    attribute_code = initial_elt.get('body')
                    attribute_dict = {}
                    attribute_dict['code'] = attribute_code
                    attribute_dict['libelle'] = attribute_libelle
                    attributes.append(attribute_dict)
                codifications[element_name] = attributes
    return codifications

def get_tableschema_diagrams(tree, nsmap=nsmap):
    diagrams = []
    for diagram in tree.findall('.//diagrams/diagram'):
        diagram_id = diagram.get('{http://schema.omg.org/spec/XMI/2.1}id')
        properties_elt = diagram.find('.//properties')
        if properties_elt.get('stereotype') == 'tableschema':
            diagram_dict = {}
            diagram_dict['id'] = diagram_id
            diagram_dict['title'] = properties_elt.get('name')
            try:
                diagram_dict['documentation'] = properties_elt.get('documentation')
            except:
                pass

            # extraction des attributs @version, @created, @modified de ./project
            project_elt = diagram.find('.//project')
            try:
                diagram_dict['version'] = project_elt.get('version')
            except:
                pass
            try:
                diagram_dict['created'] = project_elt.get('created')
            except:
                pass
            try:
                diagram_dict['modified'] = project_elt.get('modified')
            except:
                pass
            elements = []
            for element in diagram.findall('.//elements/element'):
                element_idref = element.get('subject')
                elements.append(element_idref)
            diagram_dict['elements'] = elements
            diagrams.append(diagram_dict)
    return diagrams

def clean_string(s):
    s = re.sub(r"\s+", '_', s)
    s = unicodedata.normalize('NFD', s)
    return s.encode('ascii', 'ignore').decode('ascii')

def get_tableschema_resources(application_schema_tree, dictionnaire_tree, nsmap=nsmap):
    tableschema_resources = []
    codifications = get_codifications(application_schema_tree, nsmap=nsmap)
    dictionnaire_model = get_model(dictionnaire_tree)
    elements = dictionnaire_tree.findall('.//elements/element', nsmap)
    connectors = dictionnaire_tree.find('.//connectors')
    diagrams = get_tableschema_diagrams(dictionnaire_tree, nsmap=nsmap)
    for tableschema_diagram in diagrams:
        diagram_elements = tableschema_diagram['elements']
        diagram_title = tableschema_diagram['title']
        common_dict = {}
        common_dict['$schema'] = 'https://frictionlessdata.io/schemas/table-schema.json'
        common_dict['author'] = 'Richard Mitanchey'
        common_dict['version'] = tableschema_diagram['version']
        common_dict['created'] = tableschema_diagram['created']
        common_dict['updated'] = tableschema_diagram['modified']

        resources = []
        temp_resources_dict = {}
        G = nx.DiGraph()
        for element in elements:
            element_idref = element.get('{http://schema.omg.org/spec/XMI/2.1}idref')
            if element_idref in diagram_elements:
                resource = {}
                resource_part = get_resource(element, connectors, dictionnaire_model, codifications)
                # on complète alors le schéma avec les attributs communs issus du diagram
                resource_part['schema'].update(common_dict)
                resource.update(resource_part)
                G.add_node(resource['name'])
                temp_resources_dict[resource['name']] = resource
                if 'foreignKeys' not in resource['schema'].keys():
                    continue
                FKs = resource['schema']['foreignKeys']
                if FKs is None:
                    pass
                elif type(FKs)==list:
                    for FK in FKs:
                        dest = FK['reference']['resource']
                        G.add_edge(resource['name'], dest)
                elif type(FKs)==dict:
                    dest = FKs['reference']['resource']
                    G.add_edge(resource['name'], dest)
        nodes = list(nx.algorithms.topological_sort(G))
        nodes.reverse()
        for node in nodes:
            resources.append(temp_resources_dict[node])

        tableschema_resources.append({ 'title': diagram_title, 'schemas': resources })
        del G
        del temp_resources_dict
    return tableschema_resources

with open("EolienTerrestre-conceptuel.xmi", 'rb') as f1:
    application_schema_tree = etree.parse(f1)

with open("EolienTerrestre-logique.xmi", 'rb') as f2:
    dictionnaire_tree = etree.parse(f2)

tableschemas = get_tableschema_resources(application_schema_tree, dictionnaire_tree, nsmap=nsmap)
for tableschema in tableschemas:
    title = tableschema['title']
    resources = tableschema['schemas']
    filename = clean_string(title)
    with io.open(filename+'.json', 'w+', encoding='latin1') as json_file:
        data = json.dumps(resources, ensure_ascii=False, indent=4)
        json_file.write(data)
