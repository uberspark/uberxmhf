import os
import glob
from string import Template

h_files = []#set()
c_files = []#set()
casm_files = []#set()
asm_files = []#set()

path = os.getcwd()

for dirName, subdirList, fileList in os.walk(path):
    print('Found directory: %s' % dirName)
    extension = dirName.replace(path+'/', '')
    for fname in fileList:
        if fname.endswith('.h'):
            h_files.append(extension + '/' + fname)
        elif fname.endswith('.c'):
            i = 0
            file_path = os.path.join(dirName, fname)
            os.rename(file_path, file_path+"~")
            with open(file_path+"~", "r+") as src:
                with open(file_path, 'w+') as dest:
                    for line in src:
                        i += 1
                        if i == 46:
                            dest.write("#include <uberspark/include/uberspark.h>\n")
                        elif line.startswith("#include <xmhfgeec.h>"):
                            continue
                        elif line.startswith("#include"):
                            idx = line.find('<') + 1
                            dest.write(line[:idx] + "uberspark/uobjcoll/platform/pc/uxmhf/main/include/" + line[idx:])
                        else:
                            dest.write(line)
            os.remove(file_path+"~")
            
            c_files.append(extension + '/' + fname)
        elif fname.endswith('.cS'):
            casm_files.append(extension + '/' + fname)
        elif fname.endswith('.s'):
            asm_files.append(extension + '/' + fname)

h_files.sort()
c_files.sort()
casm_files.sort()
asm_files.sort()

d = {
    'node_type': "uberspark-uobj",
    'uobj_name': "main",
    'h_files': "\n\t\t\t".join(['\"' + x + '\",' for x in h_files]),
    'c_files': "\n\t\t\t".join(['\"' + x + '\",' for x in c_files]),
    'casm_files': "\n\t\t\t".join(['\"' + x + '\",' for x in casm_files]),
    'asm_files': "\n\t\t\t".join(['\"' + x + '\",' for x in asm_files]),
    'public_methods': ""
}

with open('uberspark.json.template', 'r') as f:
    src = Template(f.read())
    manifest = src.substitute(d)
with open('uberspark.json', 'w') as f:
    f.write(manifest)

# for fi in h_files:
#     print('"' + fi + '",')
# print()

# for fi in c_files:
#     print('"' + fi + '",')
# print()

# for fi in casm_files:
#     print('"' + fi + '",')
# print()

# for fi in asm_files:
#     print('"' + fi + '",')
# print()