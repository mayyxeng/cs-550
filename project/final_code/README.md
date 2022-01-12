# `dudect`

`dudect` is an open-source tool that statistically checks whether a program is constant-time or not.
We have modified `dudect` as follows:

- Modified `dudect.h` to dump measurements to disk between program runs.
- Added `ct-verif` examples (large).
- Added `plot_cdf.py` to launch an instrumented binary and plot a CDF of its execution time under
  two environments: (1) with fixed secret inputs, and (2) with random secret inputs.

To launch all `ct-verif` tests using `dudect`'s methodology, please perform the following steps:

```bash
tar -xf dudect_orig.tar
cd dudect
git apply ../dudect_changes.path
make
# Each benchmark uses a 2m timeout (parameter `120` to `plot_cdf.py`). Many finish before that threshold is met, but
# some do need that large of a delay to gather enough program executions (otherwise the result will not be statistically
# significant).
# A sub-directory is created for every benchmark and its CDF execution time plot can be found inside.
for benchmark in dudect_aes32_-O2 dudect_aesbitsliced_-O2 dudect_chacha20_-O2 dudect_donna_-O2 dudect_donnabad_-O2 dudect_salsa20_-O2 dudect_sha256_-O2 dudect_sha512_-O2 dudect_tea_-O2; do python3 plot_cdf.py ${benchmark} ${benchmark}_res 120; done
```
