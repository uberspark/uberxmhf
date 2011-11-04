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
        elif (re.match("c.*(tx|ty).*",line)):
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
        
            #print split_comment[1]
            vns = split_comment[2].split('::')

            vl = vns[4].split('@')
            #print vl[0]
            var_pair_list.append( (split_comment[1], vl[0]) )
    
    return var_pair_list


def quantify_clauses(clause_str, var_list, num_vars):

    clause_str = clause_str.replace('\n',' ')
    clause_str = clause_str.replace('  ',' ')
    matrix = clause_str.split(' 0 ')
    
    input_clauses_list = []
    output_clauses_list = []

    keep_clause = True
    new_matrix = []

    for clause in matrix:
        if clause.strip():
            keep_clause = True
            variables = clause.split(' ')

            for v in variables:
                v = v.replace('-','')

                if v == var_list[0][0]:
                    input_clauses_list.append(clause)
                    keep_clause = False

                if v == var_list[1][0]:
                    output_clauses_list.append(clause)
                    keep_clause = False

            if keep_clause is True:
                new_matrix.append(clause)
                    
    # Get unique list of vars
    i = ' '.join(input_clauses_list)
    i = i.replace('-','')
    input_var_list = list(set(i.split(' ')))

    # Remove indicator vars
    try:
        input_var_list.remove(var_list[1][0])
    except:
        pass
        #print "Warning: indicators vars " + \
        #    var_list[1][0] + " not found in input variables"

    try:
        input_var_list.remove(var_list[0][0])    
    except:
        pass
        #print "Warning: indicators vars " + \
        #    var_list[0][0] + " not found in input variables"

    input_var_list = sorted(map(int, input_var_list))

    # Get unique list of vars
    o = ' '.join(output_clauses_list)
    o = o.replace('-','')
    output_var_list = list(set(o.split(' ')))

    # Remove indicator vars
    try:
        output_var_list.remove(var_list[0][0])
    except:
        pass
        # print "Warning: indicators vars " + \
        #     var_list[0][0] + " not found in output vars"
    try:
        output_var_list.remove(var_list[1][0])
    except:
        pass
        # print "Warning: indicators vars " + \
        #     var_list[1][0] + " not found in output vars"

    output_var_list = sorted(map(int, output_var_list))

    # Check for overlap in input and output var list
    intersection = set(output_var_list) & set(input_var_list)
    if intersection:
        for x in intersection:
            input_var_list.remove(x)

    # Turn indicator vars into integer sets
    indicators = set()
    indicators.add(int(var_list[1][0].split(' ')[0]))
    indicators.add(int(var_list[0][0].split(' ')[0]))


    # Find intermediate vars
    othervars = range(1, int(num_vars))
    other_var_set = set(othervars) \
        - set(output_var_list) \
        - set(input_var_list) \
        - indicators

    return (input_var_list, output_var_list, other_var_set, new_matrix)


def main(filename):
    (num_a, num_c, clause_str, comments) = parse(filename)

    
    var_list = parse_comments(comments)

    (input_var_list, output_var_list, other_var_set, new_matrix) = \
        quantify_clauses(clause_str, var_list, num_a)

    print "p cnf " + num_a + " " + str(len(new_matrix))

    print "a " + ' '.join([str(y) for y in output_var_list]) + " 0"
    print "e " + ' '.join([str(x) for x in input_var_list])  + " " + \
        ' '.join([str(x) for x in other_var_set]) + " 0"

    for m in new_matrix:
        print m + " 0"
    
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
