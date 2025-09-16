# MoMA

[![Artifacts](https://img.shields.io/badge/Artifacts-Available-268B3A)](https://www.acm.org/publications/policies/artifact-review-and-badging-current)
[![Artifacts](https://img.shields.io/badge/Artifacts-Evaluated:Functional-EE2651)](https://www.acm.org/publications/policies/artifact-review-and-badging-current)
[![Results](https://img.shields.io/badge/Results-Reproduced-253875)](https://www.acm.org/publications/policies/artifact-review-and-badging-current)

Multi-word modular arithmetic (MoMA) decomposes large bit-width integer arithmetic into machine-word-based operations. We implemented MoMA as a rewrite system using [SPIRAL](https://spiral.net/) as an extension of [the SPIRAL NTTX package](https://www.spiral.net/software/nttx.html). For more details, please view the full paper [here](https://dl.acm.org/doi/10.1145/3696443.3708948).

Dependencies
------------

- [nvcc](https://docs.nvidia.com/cuda/cuda-compiler-driver-nvcc/) >= 11.7
- [nsys](https://developer.nvidia.com/nsight-systems) >= 2022.4.2
- [python3](https://www.python.org/about/) >= 3.8.6
- [spiral](https://www.spiral.net/) >= 8.5.0*

\**not required if you plan to use only [pre-generated code](#using-pre-generated-code)*

Build MoMA
------------

### SPIRAL Installation

Install SPIRAL following the instructions in [this guide](https://github.com/spiral-software/spiral-software) and ensure it passes all basic tests on your platform by running `make test` in the `build` directory.

### Link this repository with SPIRAL

In the `spiral-software/namespaces/packages/` subdirectory of your SPIRAL installation tree, clone this repository and its dependencies using the following commands:
```
git clone https://github.com/Naifeng/moma.git nttx
git clone -b develop https://github.com/Naifeng/spiral-package-fftx.git fftx
git clone -b develop https://github.com/Naifeng/spiral-package-simt.git simt
```

The `packages` subdirectory should then look like this:
```
packages
└────fftx
└────simt
└────nttx (this repository)
     │    README.md (this file)
     │    ...
```

Usage
-------

Once SPIRAL is installed and linked with this repository, run the following command in the `nttx/cuda/cuda-test/` directory to benchmark MoMA-based number theoretic transforms (NTTs) for a specific input bit-width:
```
bash ./benchmark.sh -d <input_bit_width>
```
Supported input bit-widths are 128, 256, 384, and 768.

If you are running the code in this repository on one of the three platforms detailed in the paper (H100, V100, RTX 4090), you can enable platform-specific performance tuning by using the `-p` option. For example, to benchmark MoMA-based NTTs on an H100, run:
```
bash ./benchmark.sh -d 128 -p h100
```

You can type `bash ./benchmark.sh -h` for a detailed description of the available options. You can also check the correctness and profiling information of the NTT code by inspecting `cuda/cuda-test/log.txt` during the benchmarking process. Note that for each batch size, the `log.txt` file will overwrite the previous one. 

<details>
  <summary>Sample output</summary>
  <ol>
     The output will be displayed in the terminal window after the benchmark script finishes running. The following is a sample output obtained on an H100 by running the command above:
     <pre>
     ================================================================================
     Results
     ================================================================================
     NTT size [log2]     Runtime per butterfly [ns]    Runtime per NTT [ns]          
     8                   0.010                         11                            
     9                   0.011                         25                            
     10                  0.012                         60                            
     11                  0.023                         256                           
     12                  0.015                         372                           
     13                  0.017                         880                           
     14                  0.014                         1623                          
     15                  0.013                         3220                          
     16                  0.013                         6806                          
     17                  0.013                         14645                         
     18                  0.014                         31897                         
     19                  0.014                         68754                         
     20                  0.015                         155018                        
     21                  0.015                         324608                        
     22                  0.014                         663467                       
</pre>
  </ol>
</details>


### Performance tuning

For optimal NTT performance, platform-specific tuning can be performed within the code generation pass. We have incorporated known performance tuning information for V100, H100, and RTX 4090 into the SPIRAL code generation pass as a knowledge base. Users can enable this tuning using the `-p` option with `benchmark.sh`. For other platforms, the `-p` option can be omitted, which will default to `-p general`.

In the future, we plan to automate the construction of the knowledge base, allowing SPIRAL to profile the target platform and automatically derive the performance tuning information. This can be achieved by integrating MoMA with [the SPIRAL profiler](https://spiral-software.github.io/spiral-software/profiler/index.html). It is noteworthy that even without platform-specific tuning, MoMA-based NTT achieves near-ASIC performance on commodity GPUs.

### Benchmark BLAS operations

Some manual editing is required to benchmark BLAS operations, in `cuda/cuda-test/`:

1. Set `benchmark_blas` to `true` in `benchmark.sh`.
2. Set `blas_op` to one of `vvadd`, `vvsub`, `vvmul`, and `axpy` in `benchmark.sh`.

You can now benchmark any supported BLAS operation by running the following command in the `cuda/cuda-test` directory:
```
bash ./benchmark.sh -d <input_bit_width>
```
Supported input bit-widths are 128, 256, 512, and 1024.

For example, to benchmark a 512-bit `axpy` operation using the above command, set `blas_op` to `axpy` in `benchmark.sh` and run:
```
bash ./benchmark.sh -d 512
```
Remember to set `benchmark_blas` to `false` in `benchmark.sh` before benchmarking NTTs.

<details>
  <summary>Sample output</summary>
  <ol>
     The sample output on a V100 is as follows:
     <pre>
     ================================================================================
     Results
     ================================================================================
     Vector size [log2]  Runtime per element [ns]      Runtime per operation [ns]    
     8                   0.805                         206                           
</pre>
  </ol>
</details>

### Using pre-generated code

This repository includes select pieces of SPIRAL-generated code, allowing you to evaluate MoMA-based NTTs and BLAS operations even without SPIRAL installed. Please refer to the `README` files in `cuda/cuda-test/ntt_code` and `cuda/cuda-test/blas_code` for more information.

Directory Overview
---------

```
nttx (this repository)
│    README.md (this file)
│    opts.gi    
│    ...
│
└────examples
│    │    mp-cuda-batch.g
│    │    mp-py.g
│ 
└────cuda
     │    init.g
     │    ...
     │
     └────cuda-test
          │    benchmark.sh
          │    ...
          │ 
          └────blas_code
          └────ntt_code
```

License
---------

Distributed under the SPIRAL License. For more details, please refer to the `LICENSE` file.