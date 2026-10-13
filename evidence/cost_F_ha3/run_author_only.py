"""run_author_only.py -- NEW wrapper (evidence lane, 2026-10-12) around the UNEDITED module c5/pd/code/pd5_circuit_v2.py.

pd5_circuit_v2.main() also compares the m=5, h=a^3 circuit with an external auditor table that is not published.
That comparison is a cross-check only: the gate counts come from build() alone.  This wrapper calls the module's own
build(), eval_table(), DAG.counts() and the DAG dump format of main(), compares each evaluated table with the AUTHOR
reference tables only, and checks counts / chain-only counts / table hash / DAG-file hash against the recorded JSON.
usage: python3 -I -B run_author_only.py RECORDED_pd5_circuit_v2.json OUTDIR
Exit 0 iff every check holds.
"""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'c5', 'pd', 'code'))
import numpy as np
import pd5_circuit_v2 as M          # unedited module (its main() is not called)

rec = json.load(open(sys.argv[1])); outd = sys.argv[2]; os.makedirs(outd, exist_ok=True)
D, A = M.DATA, M.APN
refs = {(5, False): [os.path.join(D, 'F_PD_h0_m5.npy'), os.path.join(A, 'c4', 'pd', 'data', 'F_pd_inv_m5.npy')],
        (5, True): [os.path.join(D, 'F_PD_hX3_m5.npy')],
        (7, False): [os.path.join(D, 'F_PD_h0_m7.npy')],
        (7, True): [os.path.join(D, 'F_PD_hX3_m7.npy')]}
ok = True
for m in (5, 7):
    for wh in (False, True):
        key = 'm%d_%s' % (m, 'hX3' if wh else 'h0')
        g, Am, Bv, inv, hi, b2, chain, nch = M.build(m, wh)
        T = M.eval_table(g, inv, hi, m)
        dp = os.path.join(outd, 'dag_%s_v2.json' % key)
        json.dump({'nodes': [[i, op, list(a), lb] for i, (op, a, lb) in enumerate(g.nodes)],
                   'outputs_lo': inv, 'outputs_hi': hi, 'b2': b2}, open(dp, 'w'))
        got = {'counts': g.counts(), 'chain_only_counts': nch, 'eval_table_sha256': M.sha_arr(T),
               'dag_file_sha256': M.sha_file(dp)}
        match = {os.path.relpath(p, A): bool(np.array_equal(T, np.load(p).astype(np.int64))) for p in refs[(m, wh)]}
        same = {k: got[k] == rec[key][k] for k in got}
        good = all(match.values()) and all(same.values())
        ok &= good
        print(key, json.dumps(got['counts']), 'author_tables_match', json.dumps(match), 'equal_to_record', json.dumps(same),
              'OK' if good else 'FAIL', flush=True)
print('AUTHOR_ONLY=' + ('PASS' if ok else 'FAIL'))
sys.exit(0 if ok else 1)
