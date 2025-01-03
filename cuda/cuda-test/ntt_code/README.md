# Benchmark Pre-Generated NTTs

Disable the SPIRAL code generation by setting the following line in `cuda/cuda-test/benchmark.sh`:
```
code_gen="false"
```

We have pre-generated many pieces of NTT code for different input bit-widths and NTT sizes, stored in the `cuda/cuda-test/ntt_code` directory. For example, `ntt1024x124_h100.cu` stores a 1,024-point NTT with a 128-bit input bit-width (using a modulus of 124 bits), fine-tuned for H100.

To benchmark the stored NTT code, it is recommended to type `bash ./benchmark.sh -h` in the `cuda/cuda-test/` directory for a better understanding of each parameter that the benchmarking script accepts. Then, follow these steps:

1. Place the pre-generated code under `cuda/cuda-test/` and rename it to `ntt.cu`.
2. In the `cuda/cuda-test/` directory, run `benchmark.sh` using the respective NTT size (ensure that `$min_ntt_size` and `$max_ntt_size` are the same, as we are testing only one piece of NTT code) and input bit-width. You can modify the batch size (`$min_batch_size` and `$max_batch_size`); here we use the pre-generated code in `ntt1024x124_h100.cu` and set the batch size to range from 1 to $2^{20}$:
```
bash ./benchmark.sh mp-cuda-batch.g mxpntt.cu mxpntt 10 10 0 20 128 124 64
```

In this example, the script will benchmark the pre-generated 1,024-point NTT code for an input bit-width of 128 bits. The NTT code will run from batch size 1 to batch size $2^{20}$, or stop if the NTT code does not compile or produces a segmentation fault, indicating that the GPU resources are being exhausted in an attempt to reach the maximum batch size. Note that setting the `-p` option will not have any effect here, as the code is already pre-generated and fine-tuned for the H100.

<details>
  <summary>Sample output</summary>
  <ol>
     The output will be displayed in the terminal window after the benchmark script finishes running. The following is a sample output obtained on an H100 by running the command above:
     <pre>
     ================================================================================
     Results
     ================================================================================
     NTT size [log2]     Runtime per butterfly [ns]    Runtime per NTT [ns]          
     10                  0.012                         60                                  
</pre>
  </ol>
</details>