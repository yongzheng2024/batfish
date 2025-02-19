import sys


def first_char_index(char, line, index):
first_index = line.find(char, index)
return first_index

def second_char_index(char, line, index):
first_index = line.find(char, index)
second_index = line.find(char, first_index + 1)
return second_index

def process_indent(indent_level):
return ' ' * (indent_level * 4)

def process_line(line, indent_level=0):
# the line is empty string
if not line:
return

# remove empty char
line = line.strip()

open_paren_flag = False
split_begin_index = 0

i = 0
for char in line:

if '(' == char and False == open_paren_flag:
open_paren_flag = True
++i

elif '(' == char and True == open_paren_flag:
split_end_index = second_char_index('(', line, split_begin_index)
with open(output_filename, 'a') as outfile:
outfile.write(process_indent(indent_level) +
line[split_begin_index:split_end_index] + "\n")
split_begin_index = split_end_index
indent_level = indent_level + 1
process_line(line[split_end_index:], indent_level)
break

elif ')' == char:
split_end_index = first_char_index(')', line, split_begin_index)
open_paren_index = first_char_index('(', line, split_begin_index)
if -1 == open_paren_index or open_paren_index > split_end_index:
indent_level = indent_level - 1
with open(output_filename, 'a') as outfile:
outfile.write(process_indent(indent_level) +
line[split_begin_index:split_end_index + 1] + "\n")
process_line(line[split_end_index + 1:], indent_level)
break
else:
with open(output_filename, 'a') as outfile:
outfile.write(process_indent(indent_level) +
line[split_begin_index:split_end_index + 1] + "\n")
process_line(line[split_end_index + 1:], indent_level)
break

elif "true" == line[i:i + 4]:
with open(output_filename, 'a') as outfile:
outfile.write(process_indent(indent_level) + line[i:i+4] + "\n")
process_line(line[i + 4:], indent_level)
break

elif "false" == line[i:i + 5]:
with open(output_filename, 'a') as outfile:
outfile.write(process_indent(indent_level) + line[i:i+5] + "\n")
process_line(line[i + 5:], indent_level)
break


def format_smt2():
with open(input_filename, 'r') as infile:
lines = infile.readlines()

for line in lines:
line = line.strip()
if line.startswith("(assert"):
process_line(line)
else:
with open(output_filename, 'a') as outfile:
outfile.write(line + "\n")


""" Begin format smt2 file program """

if len(sys.argv) < 2:
print("Usage: python3 format_smt.py <filename>")
sys.exit(1)

input_filename = sys.argv[1]
output_filename = "formatted_" + input_filename

format_smt2()
