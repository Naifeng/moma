def process_file(input_file, output_file):
    # SK
    # numbers = []
    # with open(input_file, 'r') as f_in:
    #     for line in f_in:
    #         if line.startswith("    100.0"):
    #             parts = line.split()
    #             # Find the part right after "100.0" (ignoring spaces)
    #             index = parts.index("100.0") + 1
    #             # Extract the string and remove commas
    #             value_str = parts[index].replace(",", "")
    #             # Convert to a number and add it to the list
    #             value = int(value_str)
    #             numbers.append(value)

    # SK & MK
    numbers = []
    with open(input_file, 'r') as f_in:
        for line in f_in:
            # Remove trailing spaces from each line
            line = line.rstrip()
            if line.endswith(")"):
                # print(line)
                parts = line.split()
                # Find the part right before "0.0" (ignoring spaces)
                index = parts.index("0.0") - 1
                # Extract the string and remove commas
                value_str = parts[index].replace(",", "")
                # Convert to a number and add it to the list
                value = int(value_str)
                numbers.append(value)

    # print(numbers)
    runtime = sum(numbers)
    
    # Write the numbers to the output file within square brackets and separated by commas
    with open(output_file, 'w') as f_out:
        f_out.write('[' + ', '.join(map(str, numbers)) + ']\n')
    
    try:
        # Your code that may potentially raise an error
        print(runtime)
    except Exception as e:
        print(0)  # Print 0 if there is any error
    

# Example usage:
input_file = 'log.txt'  # Replace 'input.txt' with the path to your input file
output_file = 'output.txt'  # Replace 'output.txt' with the desired output file name

process_file(input_file, output_file)

# instead of lines starting with "    100.0", I want lines ending with "0.0  ker_code0(unsigned long *, unsigned long *, unsigned long *, unsigned long *, unsigned long *)" then I want the number right before it. Change the existing script to do that