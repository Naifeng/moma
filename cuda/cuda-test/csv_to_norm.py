import csv
import math

# Set the following line to true for benchmarking BLAS operations
benchmark_blas = False

def process_csv(filename):
    # Read the CSV file
    with open(filename, 'r') as f:
        reader = csv.reader(f)
        data = list(reader)

    # Extract the batch sizes (header of the columns)
    batch_sizes = list(map(int, data[0][1:]))  # Ignore the first column (NTT batch size)
    
    # Convert each batch size to 2^batch_size
    batch_sizes = [2 ** size for size in batch_sizes]

    # Initialize a list to store the minimum normalized values
    min_values = [] # runtime per btfy
    ntt_values =[]
    ntt_sizes = []

    # Process each row (ignoring the first column)
    for row in data[1:]:
        ntt_size = int(row[0])  # The first column is the NTT size (log2)
        values = list(map(int, filter(None, row[1:])))  # Values excluding the first column and stripping empty strings

        # Normalize the values by dividing each cell value by its batch size
        normalized_values = [value / batch_size for value, batch_size in zip(values, batch_sizes)]
        ntt_values.append(min(normalized_values))
        # print(ntt_values)

        # Now normalize each value by dividing it by the NTT size (2^ntt_size)
        ntt_size_value = 2 ** ntt_size  # 2^ntt_size
        # normalized_values = [value / ntt_size_value for value in normalized_values]

        # print(ntt_size_value)

        # Normalize the runtime using the formula: runtime / (log2(ntt_size) * ntt_size / 2)
        log_ntt_size = math.log2(ntt_size_value)  # log2(ntt_size)
        normalization_factor = (log_ntt_size * ntt_size_value) / 2

        if benchmark_blas:
            normalization_factor = ntt_size_value

        # Apply the normalization to the runtime (we apply the formula to each value)
        normalized_values = [value / normalization_factor for value in normalized_values]

        # Find the minimal value in the normalized values for the row
        min_values.append(min(normalized_values))
        ntt_sizes.append(ntt_size)

    # Round min_values to 3 significant digits
    min_values = [float("{:.3f}".format(value)) for value in min_values]

    return min_values, ntt_values, ntt_sizes

# Define the input CSV file path
filename = 'output.csv'

# Get the minimal normalized values for each row
min_values, ntt_values, ntt_sizes = process_csv(filename)

# Output the result
print("\n" + "=" * 80)
print("Results")
print("=" * 80)
if not benchmark_blas:
    print(f"{'NTT size [log2]':<20}{'Runtime per butterfly [ns]':<30}{'Runtime per NTT [ns]':<30}")
    for size, runtime, ntt_runtime in zip(ntt_sizes, min_values, ntt_values):
        print(f"{size:<20}{runtime:<30.3f}{int(ntt_runtime):<30}")
else:
    print(f"{'Vector size [log2]':<20}{'Runtime per element [ns]':<30}{'Runtime per operation [ns]':<30}")
    for size, runtime, ntt_runtime in zip(ntt_sizes, min_values, ntt_values):
        print(f"{size:<20}{runtime:<30.3f}{int(ntt_runtime):<30}")