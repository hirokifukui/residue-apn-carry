# evidence/_tools
New helper files written for the evidence set (not historical code):
- `cmp_lines.py`: recorded log lines must appear in a re-run's stdout (exact text and integers; floats to 1e-9; timing fields ignored).
- `cmp_json.py`: JSON comparison with the same rules.
- `rep_lib.sh`: shell helpers used by every `evidence/<row>/rep.sh`; `home_link` maps the hard-coded historical path
  `~/Library/CloudStorage/Dropbox/Scripts/Champagne/apn_cipher` to the row copy, only inside the throwaway HOME made by
  `run_all_representatives.sh`.
