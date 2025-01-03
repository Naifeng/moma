import csv

# Define input and output file names
input_file = "result.txt"
output_file = "output.csv"

# Read data from result.txt and store it in a dictionary
data = {}
with open(input_file, 'r') as f:
    for line in f:
        i, j, k = map(int, line.strip().split(','))
        if i not in data:
            data[i] = {}
        data[i][j] = k

# Write data to output.csv
with open(output_file, 'w', newline='') as f:
    writer = csv.writer(f)
    # Write header row
    writer.writerow([""] + list(data[min(data.keys())].keys()))
    # Write data rows
    for i in sorted(data.keys()):
        writer.writerow([i] + [data[i].get(j, "") for j in data[min(data.keys())].keys()])

print("CSV file has been created successfully.")
