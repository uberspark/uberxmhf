#! /usr/bin/python
import re
import sys
from optparse import OptionParser

def parse(filename):
    f = open(filename, 'r')

    problem_line = ""
    num_atoms = -1
    num_clauses = -1
    clause_list = ""
    comments = ""

    for line in f:
        if not line.rstrip():
            pass
        elif (re.match("c.*ty.*",line)):
            comments += line
        elif (re.match("c.*",line)):
            pass
        elif (re.match("p\s+cnf\s+(?P<num_atoms>\d+)\s+(?P<num_clauses>\d+)",line)):

            m = re.match("p\s+cnf\s+(?P<num_atoms>\d+)\s+(?P<num_clauses>\d+)",line)

            num_atoms = m.group('num_atoms')
            num_clauses = m.group('num_clauses')
            
            problem_line = line
        elif (re.match("\s*(-\d+|\d+)\s.*",line)):
            clause_list = clause_list + line
        else:
            print "Error, line skipped: " + line
            f.close()
            sys.exit()

    f.close()

    return (num_atoms, num_clauses, clause_list, comments)


def parse_comments(comments):
    # c -36  c::$file::test::1::tx@1#1
    # c -131 c::$file::test::1::ty@1#1

    comment_list = comments.split('\n')

    var_pair_list = [] 

    for c in comment_list:
        if c.rstrip():
            c = c.replace('\s+', ' ')
            c = c.replace('-','')
        
            split_comment = c.split(' ')
            vns = split_comment[2].split('::')
            vl = vns[4].split('@')

            var_pair_list.append( (split_comment[1], vl[0]) )
    
    return var_pair_list


def quantify_clauses(clause_str, universal_var, var_list, num_vars):

    clause_str = clause_str.replace('\n',' ')
    clause_str = clause_str.replace('  ',' ')
    matrix = clause_str.split(' 0 ')

    # Turn indicator vars into integer sets
    indicators = set()

    for i in (range(0,len(var_list))):
        indicators.add(int(var_list[i][0]))

    output_clauses_list = []
    keep_clause = True
    new_matrix = []

    for clause in matrix:
        if clause.strip():
            keep_clause = True
            variables = clause.split(' ')

            for v in variables:
                v = v.replace('-','')

                if v == universal_var:
                    output_clauses_list.append(clause)
                    keep_clause = False

                if int(v) in indicators:
                    keep_clause = False

            if keep_clause is True:
                new_matrix.append(clause)
                    
    # Get unique list of vars
    o = ' '.join(output_clauses_list)
    o = o.replace('-','')
    output_var_list = list(set(o.split(' ')))

    # Remove indicator vars
    try:
        if universal_var in output_var_list:
            output_var_list.remove(universal_var)
    except:
        print "Warning: indicators vars " + \
            universal_var + " not found in output vars"
        f.close()
        sys.exit()

    output_var_list = sorted(map(int, output_var_list))

    # # Check for overlap in input and output var list
    intersection = set(output_var_list) & indicators
    if intersection:
        for x in intersection:
            output_var_list.remove(x)

    # Vars to existentially quantify over 
    existential_vars = range(1, int(num_vars))
    ext_var_set = set(existential_vars) \
        - set(output_var_list) \
        - indicators

    return (output_var_list, ext_var_set, new_matrix)


def main(filename):
    (num_a, num_c, clause_str, comments) = parse(filename)
    
    var_list = parse_comments(comments)
    
    for row in var_list:
        universal_indicator = row[0]
        tmp_var_list = list(var_list)
        tmp_var_list.remove(row)
        (output_var_list, ext_var_set, new_matrix) = \
            quantify_clauses(clause_str, universal_indicator, tmp_var_list, num_a)

        f = open('out_' + row[1] + '.qdimacs', 'w')
        
        f.write("p cnf " + num_a + " " + str(len(new_matrix)) + '\n')
        f.write("a " + ' '.join([str(y) for y in output_var_list]) + " 0\n")
        f.write("e " + ' '.join([str(x) for x in ext_var_set]) + " 0\n")

        for m in new_matrix:
            f.write(m + " 0\n")
    
    return 


if __name__ == "__main__":

    usage = "usage: quantify -f <file_name>"
    parser = OptionParser(usage)
    parser.add_option("-f", "--file", dest="filename",
                      help="read input from FILE", metavar="FILE")

    (options, args) = parser.parse_args()


    if options.filename is None:
        parser.error("Incorrect number of arguments.")    

    main(options.filename)
