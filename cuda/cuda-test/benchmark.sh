#!/bin/bash

# Default values
platform="general"
insize=""
script=""
test_file=""
test_obj=""
min_ntt_size=""
max_ntt_size=""
min_batch_size=""
max_batch_size=""
mbits=""
basesize=""
recursionLevel=""

######################################################################
#                     Manual Configurations
######################################################################

# Set the following line to false to disable SPIRAL code generation
code_gen="true"

# Set the following line to "true" to benchmark BLAS operations
benchmark_blas="false"
# Choose from {vvadd, vvsub, vvmul, axpy}
blas_op="vvadd"

######################################################################
#                     End of Manual Configurations
######################################################################

# Print help message
show_help() {
    echo "Usage: bash ./benchmark.sh [OPTIONS] <script> <test_file> <test_obj> <min_ntt_size> <max_ntt_size> <min_batch_size> <max_batch_size> <insize> <mbits> <basesize>"
    echo
    echo "Example usage:"
    echo "  bash ./benchmark.sh -d 128"
    echo "  bash ./benchmark.sh -d 128 -p h100"
    echo "  bash ./benchmark.sh mp-cuda-batch.g mxpntt.cu mxpntt 2 3 4 5 256 252 64"
    echo "  bash ./benchmark.sh -p h100 mp-cuda-batch.g mxpntt.cu mxpntt 8 8 15 15 128 124 64"
    echo
    echo "Arguments:"
    echo "  <script>         - Path to the SPIRAL script to run"
    echo "  <test_file>      - The test file to use"
    echo "  <test_obj>       - The test object"
    echo "  <min_ntt_size>   - The minimum NTT size [log2]"
    echo "  <max_ntt_size>   - The maximum NTT size [log2]"
    echo "  <min_batch_size> - The minimum batch size [log2]"
    echo "  <max_batch_size> - The maximum batch size [log2]"
    echo "  <insize>         - The general input bit-width (mbits rounded up)"
    echo "  <mbits>          - The actual input modulus bit-width"
    echo "  <basesize>       - The base bit-width"
    echo
    echo "Options:"
    echo "  -d <insize>       Use default settings with specified input size in {128, 256, 384, 768}."
    echo "  -p <platform>     Specify the platform to be used in {h100, v100, rtx4090, general}."
    echo "  -h                Show this help message and exit."
}

# Check if no arguments are passed
if [[ $# -eq 0 ]]; then
    show_help
    exit 1
fi

# Parse options
while getopts ":d:p:h" opt; do
    case $opt in
        d)
            # Use default settings with specified insize
            insize=$OPTARG
            script="mp-cuda-batch.g"
            test_file="mxpntt.cu"
            test_obj="mxpntt"
            min_ntt_size=8
            max_ntt_size=22
            min_batch_size=0
            max_batch_size=20
            mbits=$((insize - 4))
            basesize=64
            echo "Running with default settings: insize=${insize}"
            if [ "$benchmark_blas" = "true" ]; then
                min_ntt_size=$(echo "7 + l(1024 / $insize) / l(2)" | bc -l | awk '{print int($1 + 0.5)}')
                max_ntt_size=$(echo "7 + l(1024 / $insize) / l(2)" | bc -l | awk '{print int($1 + 0.5)}')
                min_batch_size=$(echo "13 - l(1024 / $insize) / l(2)" | bc -l | awk '{print int($1 + 0.5)}')
                max_batch_size=$(echo "13 - l(1024 / $insize) / l(2)" | bc -l | awk '{print int($1 + 0.5)}')
            fi
            ;;
        p)
            # Set platform
            platform=$OPTARG
            ;;
        h)
            # Show help and exit
            show_help
            exit 0
            ;;
        *)
            echo "Invalid option: -$OPTARG" >&2
            show_help
            exit 1
            ;;
    esac
done

# Shift out processed options
shift $((OPTIND - 1))

# If positional arguments are provided
if [[ $# -ge 9 ]]; then
    # Positional arguments override defaults
    script=$1
    test_file=$2
    test_obj=$3
    min_ntt_size=$4
    max_ntt_size=$5
    min_batch_size=$6
    max_batch_size=$7
    insize=$8
    mbits=$9
    basesize=${10}
fi

# Update the gpuConfig in the script based on the selected platform
if [[ -n $script ]]; then
    sed -i "s/gpuConfig := \"[^\"]*\";/gpuConfig := \"$platform\";/g" "../../examples/${script}"
fi

# Run the script with the provided or default arguments
if [[ ! -z $insize ]]; then
    echo "Running benchmarking with:
      Script: $script
      Test File: $test_file
      Test Object: $test_obj
      Min NTT Size [log2]: $min_ntt_size
      Max NTT Size [log2]: $max_ntt_size
      Min Batch Size [log2]: $min_batch_size
      Max Batch Size [log2]: $max_batch_size
      Input Size: $insize
      Mbits: $mbits
      Base Size: $basesize
      Platform: $platform"
fi

# remove existing .txt
rm -f log.txt result.txt

SECONDS=0

# Function to update `mp-cuda-batch.g` with the correct parameters
update_script_file() {
    local insize=$1
    local mbits=$2
    local basesize=$3
    
    # Check if basesize is a power of 2 between 8 and 64
    if ! [[ $basesize =~ ^(8|16|32|64)$ ]]; then
        echo "Error: basesize must be a power of 2 between 8 and 64." >&2
        return 1
    fi

	# Check if mbits is one of the allowed values
    local valid_mbits="28 60 116 124 188 244 252 316 380 444 500 508 572 636 700 764 828 892 956 1012 1020"
    if [[ ! " $valid_mbits " =~ " $mbits " ]]; then
        echo "Error: mbits must be one of the following values: $valid_mbits." >&2
        return 1
    fi

	# Check if mbits is greater than half of insize
    if [[ $mbits -le $(( insize / 2 )) ]]; then
        echo "Error: mbits must be greater than half of insize." >&2
        return 1
    fi

    insize_pt=1 # insize_power_of_two
    # Keep doubling until it's greater than or equal to insize
    while (( insize_pt < insize )); do
        insize_pt=$(( insize_pt * 2 ))
    done

    # Calculate recursionLevel using bc
    local scale=10 # Precision for logarithmic calculations
    recursionLevel=$(bc -l <<< "scale=${scale}; l($insize_pt/$basesize)/l(2)")

    # Check if recursionLevel is valid (non-empty and numeric)
    if [[ -z "$recursionLevel" || ! "$recursionLevel" =~ ^[0-9.]+$ ]]; then
        echo "Error: Failed to compute recursionLevel. Check inputs." >&2
        return 1
    fi

    # Convert recursionLevel to integer (floor operation)
    recursionLevel=${recursionLevel%.*}

    echo "RecursionLevel: $recursionLevel"

    # Update insize, mbits, and recursionLevel in `mp-cuda-batch.g`
    sed -i "s/^insize := [0-9]\+;/insize := ${insize_pt};/" ../../examples/${script}
    sed -i "s/^mbits := [0-9]\+;/mbits := ${mbits};/" ../../examples/${script}
    sed -i "s/^recursionLevel := [0-9]\+;/recursionLevel := ${recursionLevel};/" ../../examples/${script}
}

# Update the script with the given parameters
update_script_file $insize $mbits $basesize

for (( i = ${min_ntt_size}; i <= ${max_ntt_size}; i++ ))
do
		ntt_size=$(( 2**$i ))
		echo "NTT Size: ${ntt_size}"
		
		if [ "$code_gen" = "true" ]
		then
		# change n in $script
		# add '' for all sed -i if running on macOS
		# e.g., sed -i '' "s/^n :=.*/n := ${ntt_size};/" ../../examples/bigint-cuda-batch.g 
		sed -i "s/^n :=.*/n := ${ntt_size};/" ../../examples/${script}

        if [ "$benchmark_blas" = "true" ]; then
            # set to 4 for BLAS operation code gen.
            sed -i "s/^n :=.*/n := 4;/" ../../examples/${script}
            sed -i "s/genBLAS := [^;]*;/genBLAS := true;/g" "../../examples/${script}"
            sed -i "s/genBLAS := [^;]*;/genBLAS := true;/g" "../../rewrite.gi"
            sed -i "s/genBLAS := [^;]*;/genBLAS := true;/g" "../rewrite.gi"
            sed -i "s/recurlevel := [0-9]*;/recurlevel := $recursionLevel;/g" ../../rewrite.gi
            sed -i "/^[[:space:]]*# ${blas_op}:/ {n; s/^\([[:space:]]*\)#/\1/;}" ../../rewrite.gi
            sed -i "/^[[:space:]]*# ${blas_op}:/ {n; s/^\([[:space:]]*\)#/\1/;}" ../rewrite.gi
        fi

		# change nbatch in $script
		# hard-coded to 2 and change later
		sed -i "s/^nbatch :=.*/nbatch := 2;/" ../../examples/${script}

		cd ../../../../../bin/
		# generate ntt code
		./spiral < ../namespaces/packages/nttx/examples/${script} &> /dev/null
		cd ../namespaces/packages/nttx/cuda/cuda-test
        fi

		# remove generated code
		sed -i '/BEGIN of SPIRAL/,/\END of SPIRAL/{/BEGIN of SPIRAL/!{/\END of SPIRAL/!d;};}' ./${test_file}

		# insert generated code into test cuda file
		sed -i '/BEGIN of SPIRAL/r ntt.cu' ${test_file}

		# change N
		sed -i "s/^\#define N .*/\#define N ${ntt_size}/" ./${test_file}

		# change MBITS in ap_int.h
		insize_pt=1 # insize_power_of_two
		# Keep doubling until it's greater than or equal to insize
		while (( insize_pt < insize )); do
			insize_pt=$(( insize_pt * 2 ))
		done
		sed -i "s/^\#define MBITS .*/\#define MBITS ${insize_pt}/" ./ap_int.h
        
        if [ "$code_gen" = "true" ] && [ "$ntt_size" -le 32768 ]
		then
            # automatically generate testing data
            sed -i "s/n := [0-9]\+;/n := ${ntt_size};/" ../../examples/mp-py.g

            if [ "$benchmark_blas" = "true" ]; then
                # set to 4 for BLAS operation code gen.
                sed -i "s/n := [0-9]\+;/n := 4;/" ../../examples/mp-py.g
                sed -i "s/genBLAS := [^;]*;/genBLAS := false;/g" "../../examples/${script}"
            fi

            cd ../../../../../bin/
            # generate ntt code
            ./spiral < ../namespaces/packages/nttx/examples/mp-py.g &> /dev/null
            cd ../namespaces/packages/nttx/cuda/cuda-test

            if [ "$benchmark_blas" = "true" ]; then
                sed -i "s/genBLAS := [^;]*;/genBLAS := false;/g" "../../rewrite.gi"
                sed -i "s/genBLAS := [^;]*;/genBLAS := false;/g" "../rewrite.gi"
                sed -i "/^[[:space:]]*# ${blas_op}:/ {n; s/^[[:space:]]*/&#/;}" ../../rewrite.gi
                sed -i "/^[[:space:]]*# ${blas_op}:/ {n; s/^[[:space:]]*/&#/;}" ../rewrite.gi
            fi

            # remove generated code
            sed -i '/BEGIN of SPIRAL/,/\END of SPIRAL/{/BEGIN of SPIRAL/!{/\END of SPIRAL/!d;};}' ./gen_data.py

            # insert generated code into gen_data.py
            sed -i '/BEGIN of SPIRAL/r ntt.py' gen_data.py

            # remove comment signs around testing data
            sed -i "/N: ${mbits} begin/{n;d;}" ./gen_data.py
            sed -i "/N: ${mbits} end/{n;d;}" ./gen_data.py

            # Update N, InSize and BaseSize to match the value of ntt_size
            sed -i "s/^N = [0-9]\+/N = ${ntt_size}/" ./gen_data.py
            sed -i "s/^InSize = [0-9]\+/InSize = ${insize_pt}/" ./gen_data.py
            sed -i "s/^BaseSize = [0-9]\+/BaseSize = ${basesize}/" ./gen_data.py

            python3 gen_data.py

            # insert generated data into test cuda file
            sed -i '/BEGIN of Testing Data/r data.txt' mxpntt.cu
        else
            # using existing testing data stored in mxpntt.cu
            # remove comment signs around testing data
            sed -i "/N: ${insize} begin/{n;d;}" ./${test_file}
            sed -i "/N: ${insize} end/{n;d;}" ./${test_file}

            sed -i "/testing data begin/{n;d;}" ./${test_file}
            sed -i "/testing data end/{n;d;}" ./${test_file}
        fi

		# if __device__ memory is used, change [#] to [N*InRatio*NBATCH]
		sed -i "s/__device__ uint${basesize}_t T\([0-9]\+\).*/__device__ uint${basesize}_t T\1[N*InRatio*NBATCH];/g" ./${test_file}

		for (( j = ${min_batch_size}; j <= ${max_batch_size}; j++ ))
		do
			# batch_size=$j
			batch_size=$(( 2**$j ))
			echo "Batch Size: ${batch_size}"

			# change NBATCH in $test_file
			sed -i "s/^\#define NBATCH.*/\#define NBATCH ${batch_size}/" ./${test_file}

			# change batch_size $test_file kernel
			sed -i "s/g\([0-9]\+\)(\([0-9]\+\), 1, 1)/g\1(${batch_size}, 1, 1)/g" ./${test_file}

			# compile
			# -w: disable warnings
			# nvcc ${test_file} -w -o ${test_obj}
			# -Xcompiler -mcmodel=medium -Xcompiler \"-Wl,--no-relax\": solves failed to convert GOTPCREL relocation; relink with --no-relax
			errmsg=$(nvcc ${test_file} -o ${test_obj} -w -Xcompiler -mcmodel=medium -Xcompiler \"-Wl,--no-relax\" 2>&1)
			
			if [ "$errmsg" = "" ]
			then
				# remove existing .txt
				rm -f log.txt

				# profile
				nsys nvprof ./${test_obj} &>> log.txt

				# python3 prune.py
				runtime=$(python3 prune.py 2>&1)

				if [ "$runtime" = "0" ]
				then
					# runtime error
					j=${max_batch_size} # ends the loop
				else
					echo "$i,$j,$runtime" >> result.txt
				fi
			else
				# print error message
				echo "$errmsg"

				# compile error
				j=${max_batch_size} # ends the loop
			fi
			
		done

        # put back comment signs around testing modulus and mu in gen_data.py
        if [ "$code_gen" = "true" ] && [ "$ntt_size" -le 32768 ]
		then
            sed -i "s/N: ${mbits} begin/&\n'''/" ./gen_data.py
            sed -i "s/N: ${mbits} end/&\n'''/" ./gen_data.py

            # remove generated data
            sed -i '/BEGIN of Testing Data/,/\END of Testing Data/{/BEGIN of Testing Data/!{/\END of Testing Data/!d;};}' ./mxpntt.cu
        else
            # put back comment signs around testing data
            sed -i "s/N: ${insize} begin/&\n\/\*/" ./${test_file}
            sed -i "s/N: ${insize} end/&\n\*\//" ./${test_file}

            sed -i "s/testing data begin/&\n\t\/\*/" ./${test_file}
            sed -i "s/testing data end/&\n\t\*\//" ./${test_file}
        fi

		# remove reports generated by nsys
		rm report*.sqlite
		rm report*.nsys-rep

done

python3 result_to_csv.py

if [ "$benchmark_blas" = "true" ]; then
    # Use sed to update the line in csv_to_norm.py
    sed -i 's/benchmark_blas = False/benchmark_blas = True/' csv_to_norm.py
fi

# output.csv to normalized runtime
python3 csv_to_norm.py

if [ "$benchmark_blas" = "true" ]; then
    # Use sed to update the line in csv_to_norm.py
    sed -i 's/benchmark_blas = True/benchmark_blas = False/' csv_to_norm.py
fi

duration=$SECONDS
echo "$((duration / 60)) minutes and $((duration % 60)) seconds elapsed."

