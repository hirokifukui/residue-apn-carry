"""C5 ATK lane runs v2 (uses atk_fullblind_v2: pairwise disjoint slices) (P5-10 full-blind calibration, P5-03 small-group candidate checks).
usage:
  python3 -I -B atk_runs.py true  OUT.json TABLE m w KEY0 NKEYS S1,S2,..     real cipher, key unknown to the attack
  python3 -I -B atk_runs.py rand  OUT.json TABLE m w KIND TRIAL0 NTRIALS S     KIND = RF | RP (uniform random oracle)
  python3 -I -B atk_runs.py literal OUT.json TABLE m w S ORACLES             all N^{3w} theta evaluated literally
TABLE = file stem in c5/attack/results/data.  Order: attack(query, Public) -> commit hash -> reveal -> score.
"""
import os, sys, json, time, math, hashlib
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import numpy as np
from fractions import Fraction
from atk_common import (build_cipher, Public, make_cipher_oracle, make_random_oracle, mds2, random_unit_matrix,
                        DATA, sha_arr, hypotheses, macro_ref)
from atk_fullblind_v2 import attack, commit, Kernel, G_theta, make_slices, all_tuples

T0 = time.time()


def cipher(table, m, w):
    path = os.path.join(DATA, table + '.npy')
    M = mds2() if w == 2 else random_unit_matrix(macro_ref.Ring(m), w, 0)
    return build_cipher(m, w, path, M), M, path


def bounds(N, w, s):
    rf = Fraction(N) ** ((3 - s) * w)
    sw = Fraction(math.comb(s * N, 2), N ** w)
    return {'RF_bound_N^{(3-s)w}': str(rf), 'RF_bound_float': float(rf),
            'RP_bound_N^{(3-s)w}+C(sN,2)/N^w': str(rf + sw), 'RP_bound_float': float(rf + sw),
            'RP_bound_vacuous(>=1)': bool(rf + sw >= 1)}


def literal_accept(ker, theta, Ys, m):
    for Y in Ys:
        out = G_theta(ker, theta, Y)
        for o in out:
            if any(int((((o >> i) & 1) + 2 * ((o >> (m + i)) & 1)).sum()) % 4 for i in range(m)):
                return False
    return True


def score_true(c, pub, ker, k, res, s, slice_seed):
    rg, N, w, m = c.rg, pub.N, pub.w, pub.m
    cvec = [int(v[0]) for v in rg.mat_apply(pub.M3inv, [np.array([v]) for v in k['L3']])]
    th = {'K4': [kk[0] for kk in k['K4']], 'c': cvec, 'K3': [kk[0] for kk in k['K3']]}
    slices, _ = make_slices(N, w, s, slice_seed)
    Ys = [c.enc(q, k) for q in slices]
    true_after = []
    for t in range(s):
        true_after.append(literal_accept(ker, th, Ys[:t + 1], m))
    # equivalence: G_theta == G_true on all of R^w
    X = all_tuples(N, w); xs = [X[:, j] for j in range(w)]
    Gt = G_theta(ker, th, xs); Gt_h = sha_arr(np.stack(Gt))
    cands = res['candidates']; eq = 0; is_true = 0; fn_hashes = set()
    for cd in cands:
        if cd == th: is_true += 1; fn_hashes.add(Gt_h); continue
        h = sha_arr(np.stack(G_theta(ker, cd, xs))); fn_hashes.add(h)
        eq += (h == Gt_h)
    complete = res['n_candidates_enumerated'] == res['theta_accepted_after_slice'][-1]
    wrong = len(cands) - is_true - eq
    if not res['candidate_exists']: verdict = 'NO_CANDIDATE (true lost)'
    elif is_true == 0: verdict = 'TRUE_LOST'
    elif len(cands) == 1: verdict = 'UNIQUE_TRUE'
    elif wrong == 0 and complete: verdict = 'UNIQUE_UP_TO_EQUIVALENT_MAP'
    else: verdict = 'AMBIGUOUS'
    # (c) literal theta-wise acceptance vs factorized membership on samples (only if enumeration complete)
    rng = np.random.default_rng([510, 3, slice_seed, s]); agree = disagree = 0
    if complete:
        cset = {json.dumps(cd, sort_keys=True) for cd in cands}
        sample = [{'K4': [int(v) for v in rng.integers(0, N, w)], 'c': [int(v) for v in rng.integers(0, N, w)],
                   'K3': [int(v) for v in rng.integers(0, N, w)]} for _ in range(300)] + cands[:200] + [th]
        for cd in sample:
            lit = literal_accept(ker, cd, Ys, m); fac = json.dumps(cd, sort_keys=True) in cset
            agree += lit == fac; disagree += lit != fac
    oracle_P = all(int(v) == 0 for q in slices for st in [c.states(q, k)] for jj in range(w)
                   for v in [sum(0 for _ in [])] ) if False else None
    return {'true_theta': th, 'true_retained_after_slice': true_after, 'n_candidates': len(cands),
            'candidates_enumeration_complete': complete, 'true_in_candidates': bool(is_true),
            'equivalent_map_candidates(not true, same G)': int(eq), 'wrong_candidates(different G)': int(wrong),
            'distinct_maps_among_candidates': len(fn_hashes), 'verdict': verdict,
            'literal_vs_factorized_sample': {'agree': agree, 'disagree': disagree}}


def run_true(outp, table, m, w, key0, nkeys, slist):
    c, M, path = cipher(table, m, w); pub = Public(c); ker = Kernel(pub)
    out = {'mode': 'true', 'table': table, 'table_sha256': sha_arr(np.load(path)), 'hyp': hypotheses(np.load(path), m),
           'm': m, 'w': w, 'N': pub.N, 'M': M, 'runs': []}
    for ks in range(key0, key0 + nkeys):
        for s in slist:
            q, rev, cnt = make_cipher_oracle(c, ks)                       # fresh oracle (same key seed)
            res = attack(q, pub, s, slice_seed=ks, batch=256)            # <-- attack: no key access
            h = commit(res); res['commit_sha256_before_reveal'] = h
            res['oracle_query_counter'] = cnt['queries']
            k = rev()                                                    # reveal only after commit
            res['score'] = score_true(c, pub, ker, k, res, s, ks)
            res['bounds'] = bounds(pub.N, w, s)
            res['candidates'] = res['candidates'][:20]
            out['runs'].append({'key_seed': ks, **res})
            print(table, 'key', ks, 's', s, res['K4_tuples_alive_after_slice'], res['theta_accepted_after_slice'],
                  res['score']['verdict'], res['score']['true_retained_after_slice'], res['T_wall_s'], flush=True)
            json.dump(out, open(outp, 'w'), indent=1, default=str)
    out['seconds'] = round(time.time() - T0, 1); json.dump(out, open(outp, 'w'), indent=1, default=str)
    print('DONE', out['seconds'])


def run_rand(outp, table, m, w, kind, trial0, ntrials, s):
    c, M, path = cipher(table, m, w); pub = Public(c); N = pub.N
    out = {'mode': 'rand', 'kind': kind, 'table': table, 'm': m, 'w': w, 'N': N, 's': s, 'M': M,
           'bounds_by_s': {t: bounds(N, w, t) for t in range(1, s + 1)}, 'trials': []}
    acc = [0] * s; th_sum = [0] * s
    for tr in range(trial0, trial0 + ntrials):
        q, _, cnt = make_random_oracle(N, w, tr, kind)
        res = attack(q, pub, s, slice_seed=10000 + tr, batch=256)
        for t in range(s):
            acc[t] += res['theta_accepted_after_slice'][t] > 0; th_sum[t] += res['theta_accepted_after_slice'][t]
        out['trials'].append({'trial': tr, 'theta_after_slice': res['theta_accepted_after_slice'],
                              'K4_alive': res['K4_tuples_alive_after_slice'], 'T_wall_s': res['T_wall_s'],
                              'queries': cnt['queries']})
        if (tr - trial0) % 20 == 0:
            print(kind, table, 'trial', tr, acc, round(time.time() - T0, 1), flush=True)
            out['accept_count_by_s'] = acc; json.dump(out, open(outp, 'w'), indent=1, default=str)
    out['accept_count_by_s'] = acc; out['n_trials'] = ntrials
    out['accept_rate_by_s'] = [a / ntrials for a in acc]
    out['mean_theta_by_s'] = [x / ntrials for x in th_sum]
    out['seconds'] = round(time.time() - T0, 1); json.dump(out, open(outp, 'w'), indent=1, default=str)
    print('DONE', acc, out['seconds'])


def run_literal(outp, table, m, w, s, oracles):
    """enumerate ALL N^{3w} theta; acceptance by literal G_theta on the full w-vector (no per-word split in the
    acceptance test), compare with the factorized attack's accepted set."""
    c, M, path = cipher(table, m, w); pub = Public(c); ker = Kernel(pub); N = pub.N; rg = c.rg
    out = {'mode': 'literal', 'table': table, 'm': m, 'w': w, 'N': N, 's': s, 'theta_space': N ** (3 * w), 'cases': []}
    for orc in oracles.split(','):
        kind, seed = orc.split(':'); seed = int(seed)
        if kind == 'E':
            q, rev, _ = make_cipher_oracle(c, seed)
        else:
            q, rev, _ = make_random_oracle(N, w, seed, kind)
        res = attack(q, pub, s, slice_seed=20000 + seed, batch=256, enum_cap=10 ** 7)
        fac = {(tuple(cd['K4']), tuple(cd['c']), tuple(cd['K3'])) for cd in res['candidates']}
        slices, _ = make_slices(N, w, s, 20000 + seed)
        q2, _, _ = (make_cipher_oracle(c, seed) if kind == 'E' else make_random_oracle(N, w, seed, kind))
        Ys = [q2(x) for x in slices]
        # literal: theta index = (K4_0..K4_{w-1}, c_0.., K3_0..) in base N; loop over K4 tuples, vectorise the rest
        rest = all_tuples(N, 2 * w)                                   # (N^{2w}, 2w): c_0..c_{w-1}, K3_0..K3_{w-1}
        lit_counts = [0] * s; lit = set(); t1 = time.time()
        for kap in all_tuples(N, w):
            alive = np.ones(rest.shape[0], bool)
            for t in range(s):
                Y = Ys[t]; V = [ker.Ginv[kap[i]][Y[i]] for i in range(w)]
                ok = alive.copy(); idx = np.nonzero(alive)[0]
                for j in range(w):
                    if idx.size == 0: break
                    Mi = pub.M3inv[j]; z = ker.MUL[Mi[0]][V[0]]
                    for i in range(1, w): z = rg.add(z, ker.MUL[Mi[i]][V[i]])
                    cj = rest[idx, j]; kj = rest[idx, w + j]
                    G = ker.Ginv[kj[:, None], rg.sub(z[None, :], cj[:, None])]          # (n_theta, N_x)
                    zero = np.ones(idx.size, bool)
                    for i in range(m):
                        zero &= ((((G >> i) & 1) + 2 * ((G >> (m + i)) & 1)).sum(1) % 4) == 0
                    ok[idx[~zero]] = False; idx = idx[zero]
                alive = ok
                lit_counts[t] += int(alive.sum())
            for r in np.nonzero(alive)[0]:
                lit.add((tuple(int(v) for v in kap), tuple(int(v) for v in rest[r, :w]), tuple(int(v) for v in rest[r, w:])))
        case = {'oracle': orc, 'factorized_theta_after_slice': res['theta_accepted_after_slice'],
                'literal_theta_after_slice': lit_counts, 'sets_equal': lit == fac,
                'candidate_exists_factorized': bool(fac), 'candidate_exists_literal': bool(lit),
                'n_final': len(lit), 'literal_seconds': round(time.time() - t1, 1), 'attack_T_wall_s': res['T_wall_s']}
        if kind == 'E':
            k = rev(); cvec = [int(v[0]) for v in rg.mat_apply(pub.M3inv, [np.array([v]) for v in k['L3']])]
            tt = (tuple(kk[0] for kk in k['K4']), tuple(cvec), tuple(kk[0] for kk in k['K3']))
            case['true_in_literal'] = tt in lit
        out['cases'].append(case); print(case, flush=True)
        json.dump(out, open(outp, 'w'), indent=1, default=str)
    out['seconds'] = round(time.time() - T0, 1); json.dump(out, open(outp, 'w'), indent=1, default=str)
    print('DONE', out['seconds'])


if __name__ == '__main__':
    a = sys.argv
    if a[1] == 'true':
        run_true(a[2], a[3], int(a[4]), int(a[5]), int(a[6]), int(a[7]), [int(x) for x in a[8].split(',')])
    elif a[1] == 'rand':
        run_rand(a[2], a[3], int(a[4]), int(a[5]), a[6], int(a[7]), int(a[8]), int(a[9]))
    elif a[1] == 'literal':
        run_literal(a[2], a[3], int(a[4]), int(a[5]), int(a[6]), a[7])
