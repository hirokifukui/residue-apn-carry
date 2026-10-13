# evidence/selftest -- tests of the comparison helpers (version 1.0.1)

`sh run_all_representatives.sh selftest` runs `_tools/test_cmp_json.py`: 11 cases; equal values pass, different values,
NaN, Infinity and -Infinity on either side fail, a float within the tolerance passes, a float outside fails, a bool is not
an integer, timing fields are ignored. Exit 0 iff every case behaves as expected. Not a mathematical check.
