"""Test oracle for the τ ordering model (spec 0.1 §2.3).

Each test is a Kurt-level programme: a list of contexts, each a list of
operations.  The script compiles every test for POWER (ppc.cat), ARMv8
(aarch64.cat) and C11 (rc11.cat) under the cheap mappings, runs herd7, and
prints one row per test: the required Kurt verdict and the three herd7
verdicts.  A row is flagged UNSAFE where Kurt is required to exclude an
outcome that a hardware model admits under its mapping (the mapping would
then be unsound), and NOTE where a hardware model admits what Kurt is
required to exclude only through C11 (no flag: C11 is a comparison).

Operations:
  ('st', var, val, kind)        store a constant; kind 'p' plain, 'a' atomic
  ('ld', reg, var, kind)        load into reg
  ('std', var, reg, kind)       store the value of reg (data dependency)
  ('stf', var, reg, val, kind)  store val with a false dependency on reg
  ('f', form)                   'full' guard(), 'rl' guard.rl(), 'rs' guard.rs()
  ('if', reg, k, then, else)    branch on reg == k

Usage: python3 oracle.py [ppc|arm|c11|all] [test-name-prefix]
Writes the litmus files to litmus/{ppc,arm,c11}/ and the table to table.txt.
"""
import os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
LIT = os.path.join(HERE, 'litmus')

# ---------------------------------------------------------------------------
# Mappings (the cheap ones)

PPC = dict(full=['sync'], rl=['lwsync'], rs=['lwsync'])
ARM = dict(full=['DMB ISH'], rl=['DMB ISHLD'], rs=['DMB ISHLD', 'DMB ISHST'])
# ARM alternatives for guard.rs()
ARM_ALT = {
  'storeST': dict(ARM, rs=['DMB ISHST']),
  'storeISH': dict(ARM, rs=['DMB ISH']),
}

# ---------------------------------------------------------------------------
# Tests

def P(*ops): return list(ops)

BASIC = {
 'MP':   ([[('st','x',1),('st','y',1)], [('ld','r1','y'),('ld','r3','x')]], '1:r1=1 /\\ 1:r3=0'),
 'SB':   ([[('st','x',1),('ld','r1','y')], [('st','y',1),('ld','r3','x')]], '0:r1=0 /\\ 1:r3=0'),
 'LB':   ([[('ld','r1','x'),('st','y',1)], [('ld','r3','y'),('st','x',1)]], '0:r1=1 /\\ 1:r3=1'),
 'WRC':  ([[('st','x',1)], [('ld','r1','x'),('st','y',1)], [('ld','r3','y'),('ld','r4','x')]],
          '1:r1=1 /\\ 2:r3=1 /\\ 2:r4=0'),
 'IRIW': ([[('st','x',1)], [('ld','r1','x'),('ld','r3','y')], [('st','y',1)], [('ld','r1','y'),('ld','r3','x')]],
          '1:r1=1 /\\ 1:r3=0 /\\ 3:r1=1 /\\ 3:r3=0'),
 'ISA2': ([[('st','x',1),('st','y',1)], [('ld','r1','y'),('st','z',1)], [('ld','r3','z'),('ld','r4','x')]],
          '1:r1=1 /\\ 2:r3=1 /\\ 2:r4=0'),
 '2+2W': ([[('st','x',1),('st','y',2)], [('st','y',1),('st','x',2)]], 'x=1 /\\ y=1'),
 'R':    ([[('st','x',1),('st','y',1)], [('st','y',2),('ld','r1','x')]], 'y=2 /\\ 1:r1=0'),
 'S':    ([[('st','x',2),('st','y',1)], [('ld','r1','y'),('st','x',1)]], 'x=2 /\\ 1:r1=1'),
}

# Required Kurt verdict of the weak-fence variant (guard.rl() after a
# load, guard.rs() after a store, between consecutive operations).
WEAK_REQ = {'MP': 'F', 'SB': 'A', 'LB': 'A', 'WRC': 'A', 'IRIW': 'A', 'ISA2': 'A',
            '2+2W': 'A', 'R': 'A', 'S': 'A'}

def variant(threads, v):
  out = []
  for th in threads:
    ops = []
    for k, op in enumerate(th):
      if v in ('full', 'weak') and k > 0:
        if v == 'full': ops.append(('f', 'full'))
        else: ops.append(('f', 'rl' if th[k-1][0] == 'ld' else 'rs'))
      kind = {'atomic': 'a'}.get(v, 'p')
      ops.append(op + (kind,))
    out.append(ops)
  return out

TESTS = []   # (name, family, threads, cond, required, source, why)
# source: the theorem in theories/ that decides the row for the model
FENCED = 'M2DQIfaceUse.v fenced_sc_dq'
FULL_SRC = {'SB': FENCED + '; MILitNeg.v SBf_forbidden', 'LB': FENCED + '; MILitNeg.v LBfull_forbidden',
            'IRIW': FENCED + '; MILitNeg.v IRIWf_forbidden', '2+2W': FENCED + '; MILitNeg.v W22f_forbidden',
            'R': FENCED + '; MILitNeg.v Rf_forbidden'}
TNAME = {'MP': 'MP', 'SB': 'SB', 'LB': 'LB', 'WRC': 'WRC', 'IRIW': 'IRIW', 'ISA2': 'ISA2', '2+2W': 'W22',
         'R': 'R', 'S': 'S'}
PLAIN_SRC = lambda n: 'M2DQOracleRows.v %s_plain_allowed' % TNAME[n]
WEAK_SRC = lambda n: {'MP': 'M2DQIfaceUse.v MPra_forbidden_dq', 'IRIW': 'M2DQOracleRank.v IRIW_weak_allowed',
                      '2+2W': 'M2DQOracleRank.v W22_weak_allowed'}.get(n, 'M2DQOracleRows.v %s_weak_allowed' % TNAME[n])

for name, (th, cond) in BASIC.items():
  TESTS.append((name+'.plain', name, variant(th, 'plain'), cond, 'A', PLAIN_SRC(name), 'plain: no ordering'))
  TESTS.append((name+'.atomic', name, variant(th, 'atomic'), cond, 'A', PLAIN_SRC(name), 'atomic: no ordering'))
  TESTS.append((name+'.full', name, variant(th, 'full'), cond, 'F', FULL_SRC.get(name, FENCED), 'guard() everywhere: SC'))
  TESTS.append((name+'.weak', name, variant(th, 'weak'), cond, WEAK_REQ[name], WEAK_SRC(name),
                'weak-fence verdict'))

M = []
def mixed(name, threads, cond, req, src, why):
  TESTS.append((name, 'mixed', threads, cond, req, src, why))

def weakS(th):
  out = []
  for t in th:
    ops = []
    for k, op in enumerate(t):
      if k > 0: ops.append(('f', 'rs'))
      ops.append(op + ('p',))
    out.append(ops)
  return out
mixed('LBweakS', weakS(BASIC['LB'][0]), BASIC['LB'][1], 'A', 'M2DQOracleRows.v LBweakS_allowed',
      'guard.rs() does not order R->W')
mixed('SweakS', weakS(BASIC['S'][0]), BASIC['S'][1], 'A', 'M2DQOracleRows.v SweakS_allowed',
      'guard.rs() does not order R->W')
# own-read is not a signal
mixed('FWDLD', [[('st','x',1,'p'),('ld','r1','x','p'),('f','rl'),('st','y',1,'p')],
                [('ld','r3','y','p'),('f','full'),('ld','r4','x','p')]],
      '0:r1=1 /\\ 1:r3=1 /\\ 1:r4=0', 'A', 'M2DQOracleRows.v FWDLD_allowed', 'own read is no signal')
# coherence (sc-per-location)
def CO_SRC(n, kind): return 'MILitNeg.v %s_forbidden' % n
for kind in ('p',):
  sfx = '.plain'
  mixed('CoRR'+sfx, [[('st','x',1,kind)], [('ld','r1','x',kind),('ld','r3','x',kind)]],
        '1:r1=1 /\\ 1:r3=0', 'F', CO_SRC('CoRR', kind), 'coherence')
  mixed('CoWW'+sfx, [[('st','x',1,kind),('st','x',2,kind)]], 'x=1', 'F', CO_SRC('CoWW', kind), 'coherence')
  mixed('CoRW1'+sfx, [[('ld','r1','x',kind),('st','x',1,kind)]], '0:r1=1', 'F', CO_SRC('CoRW1', kind), 'coherence')
  mixed('CoRW2'+sfx, [[('ld','r1','x',kind),('st','x',1,kind)], [('st','x',2,kind)]],
        '0:r1=2 /\\ x=2', 'F', CO_SRC('CoRW2', kind), 'coherence')
  mixed('CoWR'+sfx, [[('st','x',1,kind),('ld','r1','x',kind)], [('st','x',2,kind)]],
        '0:r1=2 /\\ x=1', 'F', CO_SRC('CoWR', kind), 'coherence')
# dependencies do not order; out of thin air is excluded
mixed('LBdata1', [[('ld','r1','x','p'),('std','y','r1','p')], [('ld','r3','y','p'),('st','x',1,'p')]],
      '0:r1=1 /\\ 1:r3=1', 'A', 'M2DQOracleRows.v LBdata1_allowed', 'dependencies do not order')
mixed('LBfalse', [[('ld','r1','x','p'),('stf','y','r1',1,'p')], [('ld','r3','y','p'),('stf','x','r3',1,'p')]],
      '0:r1=1 /\\ 1:r3=1', 'A', 'M2DQOracleRows.v LBfalse_allowed', 'false dependencies do not order')
mixed('LBfd', [[('ld','r1','y','p'),('if','r1',1,[('st','x',1,'p')],[])],
               [('ld','r3','x','p'),('f','rl'),('st','y',1,'p')]],
      '0:r1=1 /\\ 1:r3=1', 'A', 'M2DQOracleRows.v LBfd_allowed', 'a control dependency does not order')
mixed('OwnFuture', [[('ld','r1','x','p'),('st','x',1,'p'),('std','y','r1','p')],
                    [('ld','r3','y','p'),('std','x','r3','p')]],
      '0:r1=1 /\\ 1:r3=1', 'F', 'M2DQOracleOwn.v OwnFuture_forbidden_Q', 'no read of its own later write')
mixed('CoRWlate', [[('ld','r1','x','p'),('if','r1',0,[],[('st','x',2,'p'),('st','y',1,'p')])],
                   [('ld','r2','y','p'),('if','r2',1,[('st','x',1,'p')],[]),('st','x',3,'p')],
                   [('ld','r3','x','p'),('ld','r4','x','p')]],
      '0:r1=1 /\\ 1:r2=1 /\\ 2:r3=2 /\\ 2:r4=3', 'F', 'M2DQOracleCoRW.v CoRWlate_forbidden_Q', 'read-then-write coherence')
mixed('CoRWearly', [[('ld','r1','x','p'),('if','r1',0,[],[('st','x',2,'p'),('st','y',1,'p')])],
                    [('ld','r2','y','p'),('if','r2',1,[('st','x',1,'p')],[]),('st','x',3,'p')],
                    [('ld','r3','x','p'),('ld','r4','x','p')]],
      '0:r1=1 /\\ 1:r2=1 /\\ 2:r3=3 /\\ 2:r4=2', 'F', 'M2DQOracleCoRW.v CoRWearly_forbidden_Q',
      'coherence')

# A strong DRF-SC counterexample: race-free in every interleaving; the
# racy non-SC outcome is to be excluded.
mixed('DRF.C3Cex', [[('ld','r1','y','p'),('if','r1',1,[('st','x',1,'p')],
                      [('st','c',1,'p'),('ld','r2','c','p'),('if','r2',0,[('st','x',1,'p')],[])])],
                    [('ld','r3','x','p'),('if','r3',1,[('st','y',1,'p')],[])]],
      '0:r1=1 /\\ 1:r3=1', 'F', 'M2DQOracleDRF.v C3Cex_forbidden_Q', 'race-free: SC')
mixed('LBctrl1', [[('ld','r1','x','p'),('if','r1',1,[('st','y',1,'p')],[])], [('ld','r3','y','p'),('st','x',1,'p')]],
      '0:r1=1 /\\ 1:r3=1', 'A', 'M2DQOracleRows.v LBctrl1_allowed', 'dependencies do not order')
mixed('OOTA', [[('ld','r1','x','p'),('std','y','r1','p')], [('ld','r3','y','p'),('std','x','r3','p')]],
      '0:r1=1 /\\ 1:r3=1', 'F', 'M2DQOracleDRF.v OOTA_forbidden_Q', 'no value out of thin air')
mixed('OOTActrl', [[('ld','r1','x','p'),('if','r1',1,[('st','y',1,'p')],[])],
                   [('ld','r3','y','p'),('if','r3',1,[('st','x',1,'p')],[])]],
      '0:r1=1 /\\ 1:r3=1', 'F', 'M2DQOracleDRF.v OOTActrl_forbidden_Q', 'race-free: SC')

# ---------------------------------------------------------------------------
# Compilers

def regs_of(ops, acc):
  for op in ops:
    if op[0] == 'if':
      regs_of(op[3], acc); regs_of(op[4], acc)
    elif op[0] in ('st', 'std', 'stf'): acc.setdefault(op[1], None)
    elif op[0] == 'ld': acc.setdefault(op[2], None)
  return acc

class Ctr:
  def __init__(self): self.n = 0
  def lab(self, t):
    self.n += 1; return 'L%d%d' % (t, self.n)

def ppc_thread(ops, t):
  addr = regs_of(ops, {})
  for k, v in enumerate(addr): addr[v] = 'r%d' % (20 + k)
  c = Ctr(); code = []
  def emit(ops):
    for op in ops:
      o = op[0]
      if o == 'f': code.extend(PPC[op[1]]); continue
      if o == 'if':
        _, r, k, th, el = op
        le, ld = c.lab(t), c.lab(t)
        code.extend(['cmpwi %s,%d' % (r, k), 'bne %s' % le]); emit(th)
        code.extend(['b %s' % ld, '%s:' % le]); emit(el); code.append('%s:' % ld); continue
      if o == 'ld':
        _, r, v, _ = op
        code.append('lwz %s,0(%s)' % (r, addr[v]))
        continue
      if o == 'st': code.extend(['li r0,%d' % op[2], 'stw r0,0(%s)' % addr[op[1]]])
      elif o == 'std': code.append('stw %s,0(%s)' % (op[2], addr[op[1]]))
      elif o == 'stf': code.extend(['xor r9,%s,%s' % (op[2], op[2]), 'addi r9,r9,%d' % op[3],
                                    'stw r9,0(%s)' % addr[op[1]]])
  emit(ops)
  return code, addr

def arm_thread(ops, t, M):
  addr = regs_of(ops, {})
  for k, v in enumerate(addr): addr[v] = 'X%d' % (20 + k)
  c = Ctr(); code = []
  W = lambda r: 'W%d' % (int(r[1:]) + 10)
  def emit(ops):
    for op in ops:
      o = op[0]
      if o == 'f': code.extend(M[op[1]]); continue
      if o == 'if':
        _, r, k, th, el = op
        le, ld = c.lab(t), c.lab(t)
        code.extend(['CMP %s,#%d' % (W(r), k), 'B.NE %s' % le]); emit(th)
        code.extend(['B %s' % ld, '%s:' % le]); emit(el); code.append('%s:' % ld); continue
      if o == 'ld':
        _, r, v, _ = op
        code.append('LDR %s,[%s]' % (W(r), addr[v]))
        continue
      if o == 'st': code.append('MOV W0,#%d' % op[2]); src = 'W0'
      elif o == 'std': src = W(op[2])
      else: code.extend(['EOR W9,%s,%s' % (W(op[2]), W(op[2])), 'ADD W9,W9,#%d' % op[3]]); src = 'W9'
      code.append('STR %s,[%s]' % (src, addr[op[1]]))
  emit(ops)
  return code, addr

C11F = {'full': 'atomic_thread_fence(memory_order_seq_cst);',
        'rl': 'atomic_thread_fence(memory_order_acquire);',
        'rs': 'atomic_thread_fence(memory_order_release);'}
def c_thread(ops):
  addr = regs_of(ops, {})
  lines = []
  def mo(kind): return 'memory_order_relaxed'
  def emit(ops, ind):
    for op in ops:
      o = op[0]
      if o == 'f': lines.append(ind + C11F[op[1]]); continue
      if o == 'if':
        _, r, k, th, el = op
        if not th: lines.append(ind + 'if (%s != %d) {' % (r, k)); emit(el, ind + '  '); lines.append(ind + '}'); continue
        lines.append(ind + 'if (%s == %d) {' % (r, k)); emit(th, ind + '  ')
        if el: lines.append(ind + '} else {'); emit(el, ind + '  ')
        lines.append(ind + '}'); continue
      kind = op[-1]
      if o == 'ld': lines.append(ind + 'int %s = atomic_load_explicit(%s, %s);' % (op[1], op[2], mo(kind)))
      elif o == 'st': lines.append(ind + 'atomic_store_explicit(%s, %d, %s);' % (op[1], op[2], mo(kind)))
      elif o == 'std': lines.append(ind + 'atomic_store_explicit(%s, %s, %s);' % (op[1], op[2], mo(kind)))
      else: lines.append(ind + 'atomic_store_explicit(%s, %s*0+%d, %s);' % (op[1], op[2], op[3], mo(kind)))
  emit(ops, '  ')
  return lines, addr

def table(cols):
  n = max(len(c) for c in cols)
  out = [' | '.join('P%d' % i for i in range(len(cols))) + ' ;']
  for i in range(n): out.append(' | '.join((c[i] if i < len(c) else '') for c in cols) + ' ;')
  return out

def lit_ppc(name, threads, cond):
  comp = [ppc_thread(ops, t) for t, ops in enumerate(threads)]
  init = ' '.join('%d:%s=%s;' % (t, r, v) for t, (_, a) in enumerate(comp) for v, r in a.items())
  return '\n'.join(['PPC %s' % name, '{', init, '}'] + table([c for c, _ in comp]) + ['exists (%s)' % cond]) + '\n'

def lit_arm(name, threads, cond, M):
  comp = [arm_thread(ops, t, M) for t, ops in enumerate(threads)]
  init = ' '.join('%d:%s=%s;' % (t, r, v) for t, (_, a) in enumerate(comp) for v, r in a.items())
  cond = re.sub(r':r(\d+)=', lambda m: ':X%d=' % (int(m.group(1)) + 10), cond)
  return '\n'.join(['AArch64 %s' % name, '{', init, '}'] + table([c for c, _ in comp]) + ['exists (%s)' % cond]) + '\n'

def lit_c(name, threads, cond):
  allv = []
  for ops in threads:
    for v in regs_of(ops, {}):
      if v not in allv: allv.append(v)
  out = ['C %s' % name, '{ ' + ' '.join('[%s] = 0;' % v for v in allv) + ' }']
  for t, ops in enumerate(threads):
    lines, addr = c_thread(ops)
    params = ', '.join('atomic_int* %s' % v for v in addr)
    out += ['P%d (%s) {' % (t, params)] + lines + ['}']
  cond = re.sub(r'(?<![:\w])([a-z])=', r'[\1]=', cond)
  out.append('exists (%s)' % cond)
  return '\n'.join(out) + '\n'

TIMEOUT = int(os.environ.get('HERD_TIMEOUT', '900'))

def herd(model, path):
  try:
    r = subprocess.run(['herd7', '-model', model, path], capture_output=True, text=True, timeout=TIMEOUT)
  except subprocess.TimeoutExpired:
    return 'TIMEOUT'
  m = re.search(r'Observation \S+ (\w+)', r.stdout)
  return m.group(1) if m else 'ERR'

def fname(name): return name.replace('+', 'p').replace('.', '_')

def run(arch, name, threads, cond, M=ARM, tag=''):
  d = os.path.join(LIT, arch + tag); os.makedirs(d, exist_ok=True)
  p = os.path.join(d, fname(name) + '.litmus')
  if arch == 'ppc': src, model = lit_ppc(fname(name), threads, cond), 'ppc.cat'
  elif arch == 'arm': src, model = lit_arm(fname(name), threads, cond, M), 'aarch64.cat'
  else: src, model = lit_c(fname(name), threads, cond), 'rc11.cat'
  open(p, 'w').write(src)
  return herd(model, p)

def short(v): return {'Sometimes': 'S', 'Never': 'N', 'TIMEOUT': 'T/O'}.get(v, v)

if __name__ == '__main__':
  what = sys.argv[1] if len(sys.argv) > 1 else 'all'
  pre = sys.argv[2] if len(sys.argv) > 2 else ''
  rows = []
  for (name, fam, threads, cond, req, src, why) in TESTS:
    if not name.startswith(pre): continue
    if what == 'armalt':
      res = [short(run('arm', name, threads, cond, M, '-' + k)) for k, M in ARM_ALT.items()]
      print('%-16s req=%s  %s' % (name, req, '  '.join('%s=%s' % (k, r) for k, r in zip(ARM_ALT, res)))); sys.stdout.flush()
      continue
    pv = short(run('ppc', name, threads, cond))
    av = short(run('arm', name, threads, cond))
    cv = short(run('c11', name, threads, cond))
    flag = ''
    if req == 'F' and (pv == 'S' or av == 'S'): flag = 'UNSAFE'
    elif req == 'F' and cv == 'S': flag = 'c11-weaker'
    elif req == 'A' and (pv == 'N' or av == 'N' or cv == 'N'): flag = 'hw-stronger'
    row = '%-16s req=%s  POWER=%s  ARM=%s  C11=%s  %-11s  %s' % (name, req, pv, av, cv, flag, src)
    rows.append(row); print(row); sys.stdout.flush()
  if what == 'all' and not pre:
    open(os.path.join(HERE, 'table.txt'), 'w').write('\n'.join(rows) + '\n')
