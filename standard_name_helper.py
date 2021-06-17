#!/usr/bin/env python

"""
This script has several functions: 
1) check standard names from a set of host/physics metadata against the CCPPStandardNames XML list (and writes out unknown names)
2) determines the changes between two CCPPStandardNames XML lists (and writes out change files with new, replaced, and removed names)
3) bullet 2 + performing the replacement of standard names in a set of host/physics metadata (either in temporary files or overwriting existing files)

Needs: ccpp-framework as directory adjacent to script
"""

import argparse
import sys
import os.path
from xml_tools import read_xml_file
sys.path.insert(1, './ccpp-framework/scripts')
from ccpp_prebuild import import_config, gather_variable_definitions, collect_physics_subroutines
from common import decode_container, decode_container_as_dict
import difflib
import json
import re
import copy
import xml.etree.ElementTree as ET
from xml.dom import minidom

# Default path to the current (or changed) standard name dictionary
DEFAULT_STD_NM_XML = 'standard_names.xml'

# Default path to the old standard name dictionary
DEFAULT_OLD_STD_NM_XML = 'standard_names_old.xml'

DEFAULT_GEN_XML = 'standard_names_gen.xml'

# Filename of JSON file with list of host variables found in metadata but not in the standard name list (will not write if string is empty)
#JSON_UNKNOWN_HOST_FILE = ''
JSON_UNKNOWN_HOST_FILE = 'unknown_host_vars.json'

# Filename of JSON file with list of physics variables found in metadata but not in the standard name list (will not write if string is empty)
#JSON_UNKNOWN_PHYSICS_FILE = ''
JSON_UNKNOWN_PHYSICS_FILE = 'unknown_physics_vars.json'

# Filename of JSON file with list of standard name changes (will not write if string is empty)
#JSON_CHG_FILE = ''
JSON_CHG_FILE = 'standard_name_changes.json'

TEMP_TAG = '_meta_chg'

INTERACTIVE = False

GET_CLOSE_MATCHES_NONINTERACTIVE_CUTOFF = 0.5
GET_CLOSE_MATCHES_SECOND_PASS_CUTOFF = 0.7

###############################################################################
def parse_command_line(args, description):
###############################################################################
    parser = argparse.ArgumentParser(description=description,
                                     formatter_class=argparse.RawTextHelpFormatter)

    parser.add_argument('-m', '--mode', help='script mode (u=check unknown variables, c=check changed variables, m=check changed variables and modify metadata, r=use change file and modify metadata, x=generate XML file)', 
                        type=str, choices=('u','c','m','r','x'), required=True)
    parser.add_argument("config_file",
                        metavar='<config file>',
                        type=str, help="ccpp_prebuild_config.py file")
    parser.add_argument("host_base",
                        metavar='<host base dir>',
                        type=str, help="top-level directory for host model")
    parser.add_argument('-o', '--old_standard_name_file',
                        metavar='<old standard names filename>',
                        type=str, help="old XML file with standard name library",required=False,
                        default=DEFAULT_OLD_STD_NM_XML)
    parser.add_argument('-f', '--standard_name_file',
                        metavar='<standard names filename>',
                        type=str, help="XML file with (current or changed) standard name library",
                        required=False,default=DEFAULT_STD_NM_XML)
    parser.add_argument('-ov','--overwrite',     help='flag to overwrite metadata defined in the ccpp_prebuild_config.py file', action='store_true')
    parser.add_argument('-cf', '--change_file',
                        metavar='<change file filename>',
                        type=str, help="JSON file with changes to parse",
                        required=False,default=JSON_CHG_FILE)
    
    pargs = parser.parse_args(args)
    return pargs

###############################################################################
def check_unknown_vars(all_std_names, metadata_define, metadata_request, std_nm_file):
###############################################################################
    
    known_host_vars = []
    unknown_host_vars = []
    for k, v in metadata_define.items():
        if k in all_std_names:
            known_host_vars.append(k)
        else:
            unknown_host_vars.append(k)
            
    known_physics_vars =[]
    unknown_physics_vars = []
    for k, v in metadata_request.items():
        if k in all_std_names:
            known_physics_vars.append(k)
        else:
            unknown_physics_vars.append(k)
    
    print('{} of {} host variables were not found in {}'.format(len(unknown_host_vars),len(metadata_define),std_nm_file))
    for var in unknown_host_vars:
        print('unknown host var: {}'.format(var))
    if JSON_UNKNOWN_HOST_FILE:
        with open(JSON_UNKNOWN_HOST_FILE, 'w') as filehandle:
            json.dump(unknown_host_vars, filehandle)
    
    print('{} of {} physics variables were not found in {}'.format(len(unknown_physics_vars),len(metadata_request),std_nm_file))
    for var in unknown_physics_vars:
        print('unknown physics var: {}'.format(var))
    if JSON_UNKNOWN_PHYSICS_FILE:
        with open(JSON_UNKNOWN_PHYSICS_FILE, 'w') as filehandle:
            json.dump(unknown_physics_vars, filehandle)

###############################################################################
def process_diff_lines(std_name_changes, minus_lines, plus_lines):
###############################################################################
    #print(minus_lines)
    #print(plus_lines)
    #process previous set of lines
    if len(minus_lines) == len(plus_lines):
        #expect one-to-one replacement
        for i in range(len(minus_lines)):
            if 'standard_name name=' in minus_lines[i] and 'standard_name name=' in plus_lines[i]:
                std_name_changes.append((minus_lines[i].split('"')[1],plus_lines[i].split('"')[1]))
    elif len(minus_lines) == 0:
        #expect new names only
        for i in range(len(plus_lines)):
            if 'standard_name name=' in plus_lines[i]:
                std_name_changes.append(('',plus_lines[i].split('"')[1]))
    elif len(plus_lines) == 0:
        #expect deleted names only
        for i in range(len(minus_lines)):
            if 'standard_name name=' in minus_lines[i]:
                std_name_changes.append((minus_lines[i].split('"')[1],''))
    else:
        potential_removals = []
        potential_additions = []
        for i in range(len(minus_lines)):
            if 'standard_name name=' in minus_lines[i]:
                potential_removals.append(minus_lines[i].split('"')[1])
        for i in range(len(plus_lines)):
            if 'standard_name name=' in plus_lines[i]:
                potential_additions.append(plus_lines[i].split('"')[1])
        if INTERACTIVE:
            #ask the user for help deciphering changes
            processed_potential_removals = []
            for i in range(len(potential_removals)):
                print('Do any of the following names represent a replacement for "{}"? (0 for None)'.format(potential_removals[i]))
                print('0. None')
                for j in range(len(potential_additions)):
                    print('{0}. "{1}"'.format(j+1,potential_additions[j]))
                val = get_choice(range(len(potential_additions)+1))
                if int(val) > 0 and int(val) <= len(potential_additions):
                    std_name_changes.append((potential_removals[i],potential_additions[int(val)-1]))
                    processed_potential_removals.append(potential_removals[i])
                    #potential_removals.remove()
                    potential_additions.remove(potential_additions[int(val)-1])
                    #print(std_name_changes[-1])
            potential_removals = [x for x in potential_removals if x not in processed_potential_removals]
            for i in range(len(potential_removals)):
                std_name_changes.append((potential_removals[i],''))
            for j in range(len(potential_additions)):
                std_name_changes.append(('',potential_additions[j]))
        else:
            #use difflib's get_close_matches to try to figure out replacements
            processed_potential_removals = []
            for i in range(len(potential_removals)):
                close_matches = difflib.get_close_matches(potential_removals[i],potential_additions,n=1,cutoff=GET_CLOSE_MATCHES_NONINTERACTIVE_CUTOFF)
                if len(close_matches) > 0:
                    std_name_changes.append((potential_removals[i],close_matches[0]))
                    processed_potential_removals.append(potential_removals[i])
                    #potential_removals.remove(potential_removals[i])
                    potential_additions.remove(close_matches[0])
                    #print('get_close_match CHG: {} -> {}'.format(std_name_changes[-1][0],std_name_changes[-1][1]))
                else:
                    #print(potential_removals)
                    std_name_changes.append((potential_removals[i],''))
            for i in range(len(potential_additions)):
                std_name_changes.append(('',potential_additions[i]))
    
    return std_name_changes
###############################################################################
def find_changed_vars(old_file, new_file):
###############################################################################
    with open(old_file) as file_1:
        file_1_text = file_1.readlines()
  
    with open(new_file) as file_2:
        file_2_text = file_2.readlines()
    
    #first pass uses difflib's unified_diff, which relies heavily on position within the file
    
    diff_lines = difflib.unified_diff(file_1_text, file_2_text, fromfile=old_file, 
        tofile=new_file, lineterm='',n=0)
    
    std_name_changes = []
    
    minus_lines = []
    plus_lines = []
    for line in diff_lines:
        line = line.lower()
        if '@@' in line:
            std_name_changes = process_diff_lines(std_name_changes, minus_lines, plus_lines)
            
            #reset line lists
            minus_lines = []
            plus_lines = []
        elif line[0] == '-':
            minus_lines.append(line)
        elif line[0] == '+':
            plus_lines.append(line)
        else:
            print('Unrecognized line in the unified diff: {}'.format(line))
    #process the last diff hunk
    std_name_changes = process_diff_lines(std_name_changes, minus_lines, plus_lines)
        
    #second pass uses difflib's get_close_matches to look for replacements that might be out of position between the two files and for any matches for deletions (in that order)
    
    
    std_nm_replacements = [x for x in std_name_changes if x[0] and x[1]]
    std_nm_replacements_new = [x[1] for x in std_nm_replacements]
    std_nm_new = [x[1] for x in std_name_changes if not x[0] and x[1]]
    
    for r in std_nm_replacements:
        close_matches = difflib.get_close_matches(r[0],std_nm_new,n=1,cutoff=GET_CLOSE_MATCHES_SECOND_PASS_CUTOFF)
        if len(close_matches) > 0:
            print('The following close matches were found for "{0}" in the second difference pass: {1}'.format(r[0],close_matches))
            #check which match (positional or contextual) is better (use 0.0 for cutoff, since both were matches, and order of result is by similarity score)
            match_order = difflib.get_close_matches(r[0],[r[1],close_matches[0]],n=2,cutoff=0.0)
            if match_order[0] == close_matches[0]:
                #substitute the contextual replacement for the positional replacement
                if close_matches[0] not in std_nm_replacements_new:
                    #close match was a "new" standard name; remove the old replacement, make old match a new standard name, add the new replacement
                    std_name_changes.remove(r)
                    std_name_changes.append(('',r[1]))
                    std_name_changes.append((r[0],close_matches[0]))
                else:
                    #close match was part of an existing match; remove the old replacement, make old match a new standard name, make old original name a deletion, add the new replacement
                    std_name_changes.remove(r)
                    std_name_changes.append(('',r[1]))
                    close_match_orig = [x[0] for x in std_name_changes if x[1] == close_matches[0]][0]
                    std_name_changes.append((close_match_orig,''))
                    std_name_changes.append((r[0],close_matches[0]))
    
    #need to recalculate these lists because previous operation could have changed them
    std_nm_replacements = [x for x in std_name_changes if x[0] and x[1]]
    std_nm_replacements_new = [x[1] for x in std_nm_replacements]
    std_nm_new = [x[1] for x in std_name_changes if not x[0] and x[1]]
    std_nm_deletions = [x[0] for x in std_name_changes if x[0] and not x[1]]
    
    for d in std_nm_deletions:
        close_matches = difflib.get_close_matches(d[0],std_nm_new,n=1,cutoff=GET_CLOSE_MATCHES_SECOND_PASS_CUTOFF)
        if len(close_matches) > 0:
            print('The following close matches were found for "{0}" in the second difference pass: {1}'.format(d[0],close_matches))
            if close_matches[0] not in std_nm_replacements_new:
                #use the new match (remove the separate deletions and additions; add a replacement)
                std_name_changes.remove((d,''))
                std_name_changes.remove(('',close_matches[0]))
                std_name_changes.append((d,close_matches[0]))
            else:    
                #the match was already matched to something else
                close_match_orig = [x[0] for x in std_name_changes if x[1] == close_matches[0]][0]
                #check for which match (positional or contextual) has a higher string comparison score
                match_order = difflib.get_close_matches(close_matches[0],[d[0],close_match_orig],n=2,cutoff=0.0)
                if match_order[0] == d[0]:
                    std_name_changes.remove(d)
                    std_name_changes.append((close_match_orig,''))
                    std_name_changes.append((d[0],close_matches[0]))
    
    n_replacements = len([x for x in std_name_changes if x[0] and x[1]])
    n_adds = len([x for x in std_name_changes if not x[0] and x[1]])
    n_removals = len([x for x in std_name_changes if x[0] and not x[1]])
    
    return (std_name_changes, n_replacements, n_adds, n_removals)

###############################################################################
def edit_config_metadata(config_file, std_nm_replacements, overwrite):
###############################################################################
    with open(config_file,'r') as f:
        #only replace standard names in the OPTIONAL_ARGUMENTS dictionary
        newlines = []
        optional_args_start = -999
        optional_args_end = -999
        for i, line in enumerate(f.readlines()):
            newlines.append(line)
            if ("OPTIONAL_ARGUMENTS = " in line):
                optional_args_start = i
            if ("STATIC_API_DIR = " in line):
                optional_args_end = i
    
    origlines = copy.copy(newlines)
    
    if optional_args_start > 0 and optional_args_end > 0:
        for r in std_nm_replacements:
            newlines[optional_args_start:optional_args_end] = [re.sub(r'\b%s\b' % r[0], r[1], line) for line in newlines[optional_args_start:optional_args_end]]
    
        if newlines != origlines:
            if overwrite:
                new_filename = config_file
            else:
                (fn_root, fn_ext) = os.path.splitext(config_file)
                new_filename = fn_root + TEMP_TAG + fn_ext
            with open(new_filename,'w') as f:
                f.writelines(newlines)

###############################################################################
def edit_file_metadata(files, std_nm_replacements, overwrite):
###############################################################################
    
    for file in files:
        #it is assumed that we start with a list of source files (not .meta files), so construct the .meta filename
        (fn_root, fn_ext) = os.path.splitext(file)
        meta_filename = fn_root + '.meta'
        
        if os.path.isfile(meta_filename):
            #read in entire file contents
            with open(meta_filename, 'r') as f:
                contents = f.read()
            
            total_replacements = 0
            for r in std_nm_replacements:
                #replace each standard name (whole word only) in the entire contents of the file and keep track of how many names have been replaced
                (contents, n_replacements) = re.subn(r'\b%s\b' % r[0], r[1], contents)
                total_replacements += n_replacements
            
            #write out edited file if necessary, using either a temporary new metadata file or the existing metadata file
            if total_replacements > 0:
                if overwrite:
                    new_filename = meta_filename
                else:
                    (fn_root, fn_ext) = os.path.splitext(meta_filename)
                    new_filename = fn_root + TEMP_TAG + fn_ext
                with open(new_filename,'w') as f:
                    f.write(contents)

###############################################################################
def parse_change_file(change_file, host_metadata, physics_metadata):
###############################################################################
    
    with open(change_file, 'r') as filehandle:
        std_name_changes_from_file = json.load(filehandle)
    
    #validate the changes in the file (make sure that replacements have originals in standard name list)
    std_name_changes = []
    for change in std_name_changes_from_file:
        if (change[0] and change[1]) and (change[0] not in host_metadata.keys() + physics_metadata.keys()):
            print("The change {0} -> {1} cannot be implemented because {0} is not in the current host/physics metadata. Ignoring this change.".format(change[0],change[1]))
        else:
            std_name_changes.append(change)

    n_replacements = len([x for x in std_name_changes if x[0] and x[1]])
    n_adds = len([x for x in std_name_changes if not x[0] and x[1]])
    n_removals = len([x for x in std_name_changes if x[0] and not x[1]])
    
    return(std_name_changes, n_replacements, n_adds, n_removals)

###############################################################################
def create_XML(metadata_define):
###############################################################################
    
    var_names = sorted(list(set(list(metadata_define.keys()))))
    
    var_dict_by_container = {}
    #organize metadata by module and type
    for var_name in var_names:
        var = metadata_define[var_name][0]
        target = decode_container_as_dict(var.container)
        var_module = target.get('MODULE')
        var_type = target.get('TYPE')
        if var_module and var_module not in var_dict_by_container.keys():
            var_dict_by_container[var_module] = {}
        if var_module in var_dict_by_container.keys():
            if var_type:
                if var_type not in var_dict_by_container[var_module].keys():
                    var_dict_by_container[var_module][var_type] = []
            else:
                if None not in var_dict_by_container[var_module].keys():
                    var_dict_by_container[var_module][None] = []
        var_dict_by_container[var_module][var_type].append(var_name)
    
    #sort the list of var_names alphabetically
    for k1, v1 in var_dict_by_container.items():
        for k2, v2 in v1.items():
            v2 = sorted(v2)
    
    #write out the standard names to XML organized by module/type (put into separate sections); alphabetically within each section
    root = ET.Element("standard_names", name="CCPP Standard Name Library", version="1.0")
    for k1, v1 in var_dict_by_container.items():
        for k2, v2 in v1.items():
            if k2 is None:
                sec = ET.SubElement(root, "section", name=k1)
            else:
                sec = ET.SubElement(root, "section", name=k1 + '_' + k2)
            for var_name in v2:
                name = ET.SubElement(sec, 'standard_name', {'name':var_name})
                var = metadata_define[var_name][0]
                ET.SubElement(name, "type", kind=var.kind, units=var.units).text = var.type
    
    tree = minidom.parseString(ET.tostring(root)).toprettyxml(indent="   ")
    with open(DEFAULT_GEN_XML, "w") as f:
        f.write(tree)

###############################################################################
def get_choice(choices):
###############################################################################
  choice = -999
  while choice not in choices:
      choice = input("Enter your value: ")
  return choice

###############################################################################
def main_func():
###############################################################################
    """Describe ...
    """
    # Parse command line arguments
    args = parse_command_line(sys.argv[1:], __doc__)
    
    
    #Use existing functionality from the ccpp_prebuild.py script to return host + scheme metadata
    builddir = None
    (success, config) = import_config(args.config_file, builddir)
    if not success:
        raise Exception('Call to import_config failed.')
    
    #add relative paths to variable definition files and scheme files
    for idx, x in enumerate(config['variable_definition_files']):
        if not os.path.isfile(x):
            config['variable_definition_files'][idx] = args.host_base + '/' + x
    
    for idx, x in enumerate(config['scheme_files']):
        if not os.path.isfile(x):
            config['scheme_files'][idx] = args.host_base + '/' + x
    
    # Variables defined by the host model
    (success, metadata_define, dependencies_define) = gather_variable_definitions(config['variable_definition_files'], config['typedefs_new_metadata'])
    if not success:
        raise Exception('Call to gather_variable_definitions failed.')
    
    # Variables requested by the CCPP physics schemes
    (success, metadata_request, arguments_request, dependencies_request, schemes_in_files) = collect_physics_subroutines(config['scheme_files'])
    if not success:
       raise Exception('Call to collect_physics_subroutines failed.')
    
    #convert metadata keys to lower case
    for key in metadata_define.keys():
        metadata_define[key.lower()] = metadata_define.pop(key)
    for key in metadata_request.keys():
        metadata_request[key.lower()] = metadata_request.pop(key)
    
    stdname_file = os.path.abspath(args.standard_name_file)    
    _, root = read_xml_file(stdname_file)
        
    #get list of all standard names from the standard name file
    all_std_names = []
    for name in root.findall('./section/standard_name'):
        all_std_names.append(name.attrib['name'].lower())
    
    if (args.mode == 'u'):
        #just check for standard names that are in host + physics metadata but NOT in the standard name library
        check_unknown_vars(all_std_names, metadata_define, metadata_request, args.standard_name_file)
    elif (args.mode == 'x'):
        create_XML(metadata_define) #, metadata_request) #metadata_define should be a superset of metadata_request
    elif (args.mode == 'c' or args.mode == 'm'):
        #determine additions, replacements, and removals for standard names given two standard name library files
        (std_name_changes, n_replacements, n_adds, n_removals) = find_changed_vars(args.old_standard_name_file, args.standard_name_file)
        
        #print out results
        print('Detected {0} changes ({1} replacements, {2} additions, {3} removals) between {4} and {5}:'.format(len(std_name_changes),n_replacements,n_adds,n_removals,args.old_standard_name_file,args.standard_name_file))
        for chg in std_name_changes:
            if not chg[0]:
                print('NEW: {}'.format(chg[1]))
            elif not chg[1]:
                print('RM: {}'.format(chg[0]))
            else:
                print('CHG: {} -> {}'.format(chg[0],chg[1]))
        
        #write out results
        if JSON_CHG_FILE:
            #std_name_changes_dict = {}
            #for i, change in enumerate(std_name_changes):
            #    key, value = i, change
            #    std_name_changes_dict[key] = value
            with open(JSON_CHG_FILE, 'w') as filehandle:
                #json.dump(std_name_changes_dict, filehandle)
                json.dump(std_name_changes, filehandle)
    
    if (args.mode == 'r'):
        if os.path.isfile(args.change_file):
            (std_name_changes, n_replacements, n_adds, n_removals) = parse_change_file(args.change_file, metadata_define, metadata_request)
        
            print('Read {0} changes ({1} replacements, {2} additions, {3} removals) in {4}:'.format(len(std_name_changes),n_replacements,n_adds,n_removals,args.change_file))
            for chg in std_name_changes:
                if not chg[0]:
                    print('NEW: {}'.format(chg[1]))
                elif not chg[1]:
                    print('RM: {}'.format(chg[0]))
                else:
                    print('CHG: {} -> {}'.format(chg[0],chg[1]))
        else:
            print("{} is not a valid file. Exiting.".format(args.change_file))
    
    if (args.mode == 'm' or args.mode == 'r'):
        #for editing metadata files, only handle replacements for now (could extend to handle removals if necessary)
        std_nm_replacements = [x for x in std_name_changes if x[0] and x[1]]
        
        #check for and edit changed standard names in config file
        edit_config_metadata(args.config_file, std_nm_replacements, args.overwrite)
        #check for and edit changed standard names in host and physics metadata
        edit_file_metadata(config['variable_definition_files'], std_nm_replacements, args.overwrite)
        edit_file_metadata(config['scheme_files'], std_nm_replacements, args.overwrite)
        
###############################################################################
if __name__ == "__main__":
    main_func()