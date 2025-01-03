# Benchmark Pre-Generated BLAS Operations

Disable the SPIRAL code generation by setting the following line in `cuda/cuda-test/benchmark.sh`:
```
code_gen="false"
```

We have pre-generated BLAS code, stored in `cuda/cuda-test/blas_code`. For example, `axpy1024x124.cu` stores an axpy operation with 1,024 elements per vector and a 128-bit input bit-width (using a 124-bit modulus).

To benchmark the stored BLAS code:

1. Place the pre-generated code under `cuda/cuda-test/` and rename it to `ntt.cu`.
2. Set `code_gen="false"` and `benchmark_blas="true"` in `benchmark.sh`. There is no need to set `blas_op` to the corresponding BLAS operation in `benchmark.sh` since no code generation is involved.
3. Run `benchmark.sh` using the respective input bit-width:
```
bash ./benchmark.sh -d <input_bit_width>
```

For example, to benchmark `axpy1024x124.cu`, run
```
bash ./benchmark.sh -d 128
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
     10                  0.075                         76                            
</pre>
  </ol>
</details>
