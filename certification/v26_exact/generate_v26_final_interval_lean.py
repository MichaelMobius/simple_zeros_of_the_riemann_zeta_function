#!/usr/bin/env python3
"""Generate kernel-checkable rational interval certificates for v26 final cells.

Python uses Fraction only to select a finite rational partition and to check that
all requested centre-radius enclosures have positive rational margin.  The
generated Lean files reconstruct every enclosure from primitive lemmas, Taylor
bounds, and ring/norm_num, so Python is not a trusted proof oracle.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
import argparse, hashlib, json

PI_L=Q(31415926,10_000_000); PI_U=Q(31415927,10_000_000)
C_L=Q(88280819,106683860); C_U=Q(490449,592688)
J={
1:(Q(1023,1000),Q(1061,1000)),2:(Q(1950,1000),Q(2018,1000)),
3:(Q(2991,1000),Q(3061,1000)),4:(Q(3950,1000),Q(4084,1000)),
5:(Q(4962,1000),Q(5050,1000)),6:(Q(5975,1000),Q(6086,1000)),
7:(Q(6967,1000),Q(7101,1000)),8:(Q(7993,1000),Q(8080,1000)),
9:(Q(9013,1000),Q(9108,1000)),10:(Q(10025,1000),Q(10078,1000))}
M={1:Q(37,25),2:Q(723,2000),3:Q(17,125),4:Q(173,2500),5:Q(507,10000),
   6:Q(31,1000),7:Q(213,10000),8:Q(181,10000),9:Q(1,80),10:Q(117,10000)}
A={1:Q(1043,1000),2:Q(1984,1000),3:Q(3026,1000),4:Q(4018,1000),5:Q(5004,1000),
   6:Q(6045,1000),7:Q(7034,1000),8:Q(8036,1000),9:Q(9074,1000),10:Q(10052,1000)}
W={i+1:Q(v,100_000_000) for i,v in enumerate([16195,39121,254,32,186,2278,886,853,3712,1420])}
D={i+1:Q(v,10_000_000) for i,v in enumerate([-230346,-172761,8840,2381,-4542,12962,6976,5985,10801,6120])}
R={i+1:Q(v,1000) for i,v in enumerate([20,34,35,68,46,70,67,44,61,27])}
EPS=Q(1,20_000_000)
# Equal subdivisions on each side of the integer N.  These were minimized
# against the exact rational ball calculation below.
COUNTS={1:[16],2:[4,5],3:[1,14],4:[1,10],5:[1,8],6:[1,11],7:[1,12],8:[1,14],9:[8],10:[5]}

class Ball:
    def __init__(self,c,r=0):
        self.c=Q(c); self.r=Q(r)
        assert self.r >= 0
    @property
    def lo(self): return self.c-self.r
    @property
    def hi(self): return self.c+self.r
    def __add__(self,o):
        o=asball(o); return Ball(self.c+o.c,self.r+o.r)
    __radd__=__add__
    def __neg__(self): return Ball(-self.c,self.r)
    def __sub__(self,o): return self+(-asball(o))
    def __rsub__(self,o): return asball(o)-self
    def __mul__(self,o):
        o=asball(o)
        return Ball(self.c*o.c,abs(self.c)*o.r+abs(o.c)*self.r+self.r*o.r)
    __rmul__=__mul__
    def pow(self,n):
        z=Ball(1)
        for _ in range(n): z=z*self
        return z

def asball(x): return x if isinstance(x,Ball) else Ball(x)
def p7(x): return x-x**3/Q(6)+x**5/Q(120)-x**7/Q(5040)
def p9(x): return p7(x)+x**9/Q(362880)
def c10(x): return Q(1)-x*x/Q(2)+x**4/Q(24)-x**6/Q(720)+x**8/Q(40320)-x**10/Q(3628800)
def c8(x): return Q(1)-x*x/Q(2)+x**4/Q(24)-x**6/Q(720)+x**8/Q(40320)
PI=Ball((PI_L+PI_U)/2,(PI_U-PI_L)/2)
CC=Ball((C_L+C_U)/2,(C_U-C_L)/2)

def trig_balls(N,L,U):
    assert U <= N or L >= N
    if L >= N:
        lo=PI_L*(L-Q(N)); hi=PI_U*(U-Q(N)); neg=False
    else:
        lo=PI_L*(Q(N)-U); hi=PI_U*(Q(N)-L); neg=True
    assert 0 <= lo <= hi <= 1
    s=Ball((p7(lo)+p9(hi))/2,(p9(hi)-p7(lo))/2)
    c=Ball((c10(hi)+c8(lo))/2,(c8(lo)-c10(hi))/2)
    return (-s if neg else s),c

def jet_balls(N,L,U):
    x=Ball((L+U)/2,(U-L)/2); b=PI*x; s,c=trig_balls(N,L,U); C=CC
    b2=b.pow(2); b3=b.pow(3); b4=b.pow(4); b5=b.pow(5)
    H=C*PI*x*s-Q(1,2)*c
    M1=(C*b3-Q(1,2)*C*b+b)*c+(-C*b2+Q(1,2)*b2-Q(1,2)*C-Q(1,4))*s
    P2=(-2*C+Q(1,2))*b4-Q(7,2)*b2+Q(1,2)*C-Q(3,8)
    Q2=-C*b5+3*C*b3-2*b3+Q(11,4)*C*b+b
    M2=P2*c+Q2*s; den=b2-Q(1,2)
    return x,b,H,M1,M2,den

def curvature_margin(N,L,U):
    _x,_b,H,M1,M2,den=jet_balls(N,L,U)
    E=2*PI.pow(2)*(M1.pow(2)+H*M2)-M[N]*den.pow(4)
    return E.lo

def anchor_margins(N):
    x=A[N]
    _x,_b,H,M1,_M2,den=jet_balls(N,x,x)
    hw=(H.pow(2)-W[N]*den.pow(2)).lo
    num=2*PI*H*M1
    hlo=(num-(D[N]-EPS)*den.pow(3)).lo
    hup=((D[N]+EPS)*den.pow(3)-num).lo
    return hw,hlo,hup

def ql(q):
    q=Q(q)
    return f"({q.numerator} : ℝ)" if q.denominator==1 else f"({q.numerator} / {q.denominator} : ℝ)"

def partitions(N):
    L,U=J[N]
    segs=[(L,U)] if not (L<Q(N)<U) else [(L,Q(N)),(Q(N),U)]
    out=[]
    for (l,u),n in zip(segs,COUNTS[N]):
        for i in range(n):
            out.append((l+(u-l)*Q(i,n),l+(u-l)*Q(i+1,n)))
    assert all(curvature_margin(N,l,u)>0 for l,u in out)
    return out

NORM_DEFS="[v21RootPiL, v21RootPiU, v21RootCL, v21RootCU, v21RootSinLower7, v21RootSinUpper9, v21RootCosLower10, v21RootCosUpper8]"

def ball_setup(N,L,U,variable=True,need_m2=True):
    side="right" if L>=N else "left"; ls,us=ql(L),ql(U); x="x" if variable else ls
    z=[]
    if variable:
        z += [f"  have hx : v26Ball x (({ls} + {us}) / 2) (({us} - {ls}) / 2) := by",
              "    exact v26_ball_of_bounds hL hU"]
    else:
        z += [f"  have hx := v26_ball_const {ls}"]
    z += ["  have hpi := v26_pi_ball","  have hC := v26_C_ball"]
    if side=="right":
        tail=(f" (x := x) (by norm_num) hL hU (by norm_num [v21RootPiU])" if variable
              else f" (x := {ls}) (by norm_num) (by rfl) (by rfl) (by norm_num [v21RootPiU])")
        z += [f"  have hs := v26_sin_local_right_ball (N := {N}) (L := {ls}) (U := {us})"+tail,
              f"  have hc := v26_cos_local_right_ball (N := {N}) (L := {ls}) (U := {us})"+tail]
    else:
        tail=(f" (x := x) (by norm_num) hL hU (by norm_num [v21RootPiU])" if variable
              else f" (x := {ls}) (by norm_num) (by rfl) (by rfl) (by norm_num [v21RootPiU])")
        z += [f"  have hs := v26_sin_local_left_ball (N := {N}) (L := {ls}) (U := {us})"+tail,
              f"  have hc := v26_cos_local_left_ball (N := {N}) (L := {ls}) (U := {us})"+tail]
    z += [
      "  have hb0 := v26_ball_mul hpi hx",
      f"  have hb : v26Ball (v21B {x}) _ _ := by", "    simpa [v21B] using hb0",
      "  have hb2raw := v26_ball_mul hb hb",
      f"  have hb2 : v26Ball ((v21B {x}) ^ 2) _ _ := by", "    simpa [pow_two] using hb2raw",
      "  have hb3raw := v26_ball_mul hb2 hb",
      f"  have hb3 : v26Ball ((v21B {x}) ^ 3) _ _ := by", "    convert hb3raw using 1 <;> ring",
      "  have hb4raw := v26_ball_mul hb2 hb2",
      f"  have hb4 : v26Ball ((v21B {x}) ^ 4) _ _ := by", "    convert hb4raw using 1 <;> ring",
      "  have hb5raw := v26_ball_mul hb4 hb",
      f"  have hb5 : v26Ball ((v21B {x}) ^ 5) _ _ := by", "    convert hb5raw using 1 <;> ring",
      "  have hCp := v26_ball_mul hC hpi","  have hCpx := v26_ball_mul hCp hx",
      "  have hCpxs := v26_ball_mul hCpx hs",
      "  have hhalfcos := v26_ball_mul_const_left (a := (1 / 2 : ℝ)) hc",
      "  have hHraw := v26_ball_sub hCpxs hhalfcos",
      f"  have hH : v26Ball (v21RootH {N} {x}) _ _ := by","    convert hHraw using 1 <;> ring",
      "  have hCb3 := v26_ball_mul hC hb3","  have hCb := v26_ball_mul hC hb",
      "  have hhalfCb := v26_ball_mul_const_left (a := (1 / 2 : ℝ)) hCb",
      "  have hA1 := v26_ball_sub hCb3 hhalfCb","  have hA := v26_ball_add hA1 hb",
      "  have hCb2 := v26_ball_mul hC hb2","  have hnegCb2 := v26_ball_neg hCb2",
      "  have hhalfB2 := v26_ball_mul_const_left (a := (1 / 2 : ℝ)) hb2",
      "  have hhalfC := v26_ball_mul_const_left (a := (1 / 2 : ℝ)) hC",
      "  have hB1 := v26_ball_add hnegCb2 hhalfB2","  have hB2 := v26_ball_sub hB1 hhalfC",
      "  have hB := v26_ball_sub hB2 (v26_ball_const (1 / 4 : ℝ))",
      "  have hAc := v26_ball_mul hA hc","  have hBs := v26_ball_mul hB hs",
      "  have hM1raw := v26_ball_add hAc hBs",
      f"  have hM1 : v26Ball (v26LocalM1 {N} {x}) _ _ := by","    convert hM1raw using 1 <;> ring"]
    if need_m2:
        z += [
          "  have hneg2C := v26_ball_mul_const_left (a := (-2 : ℝ)) hC",
          "  have hPcoef := v26_ball_add hneg2C (v26_ball_const (1 / 2 : ℝ))",
          "  have hPlead := v26_ball_mul hPcoef hb4",
          "  have h7b2 := v26_ball_mul_const_left (a := (7 / 2 : ℝ)) hb2",
          "  have hP1 := v26_ball_sub hPlead h7b2","  have hP2 := v26_ball_add hP1 hhalfC",
          "  have hP := v26_ball_sub hP2 (v26_ball_const (3 / 8 : ℝ))",
          "  have hCb5 := v26_ball_mul hC hb5","  have hnegCb5 := v26_ball_neg hCb5",
          "  have h3Cb3 := v26_ball_mul_const_left (a := (3 : ℝ)) hCb3",
          "  have h2b3 := v26_ball_mul_const_left (a := (2 : ℝ)) hb3",
          "  have h11Cb := v26_ball_mul_const_left (a := (11 / 4 : ℝ)) hCb",
          "  have hQ1 := v26_ball_add hnegCb5 h3Cb3","  have hQ2 := v26_ball_sub hQ1 h2b3",
          "  have hQ3 := v26_ball_add hQ2 h11Cb","  have hQ := v26_ball_add hQ3 hb",
          "  have hPc := v26_ball_mul hP hc","  have hQs := v26_ball_mul hQ hs",
          "  have hM2raw := v26_ball_add hPc hQs",
          f"  have hM2 : v26Ball (v26LocalM2 {N} {x}) _ _ := by","    convert hM2raw using 1 <;> ring"]
    z += ["  have hDraw := v26_ball_sub hb2 (v26_ball_const (1 / 2 : ℝ))",
          f"  have hDb : v26Ball (v21D {x}) _ _ := by","    simpa [v21D] using hDraw"]
    return "\n".join(z)

def curvature_theorem(N,k,L,U):
    return f'''theorem v26_curvature_N{N}_cell{k} {{x : ℝ}}
    (hL : {ql(L)} ≤ x) (hU : x ≤ {ql(U)}) :
    {ql(M[N])} ≤ v26WeightXSecond x := by
  have hx89 : (89 / 100 : ℝ) < x := lt_of_lt_of_le (by norm_num) hL
  have hxcert : v17KernelCertPoint < x := by
    simpa [v17KernelCertPoint] using hx89
  have hDpos : 0 < v21D x := v21_D_pos (v21_A_lt_B_of_cert_lt hxcert)
  have hD : v21D x ≠ 0 := ne_of_gt hDpos
{ball_setup(N,L,U,True,True)}
  have hM1sq : v26Ball ((v26LocalM1 {N} x) ^ 2) _ _ := by
    simpa [pow_two] using v26_ball_mul hM1 hM1
  have hHM2 := v26_ball_mul hH hM2
  have hNum := v26_ball_add hM1sq hHM2
  have hpi2 : v26Ball (Real.pi ^ 2) _ _ := by
    simpa [pow_two] using v26_ball_mul hpi hpi
  have hscale := v26_ball_mul_const_left (a := (2 : ℝ)) hpi2
  have hLeft := v26_ball_mul hscale hNum
  have hD2 : v26Ball ((v21D x) ^ 2) _ _ := by
    simpa [pow_two] using v26_ball_mul hDb hDb
  have hD4 : v26Ball ((v21D x) ^ 4) _ _ := by
    convert v26_ball_mul hD2 hD2 using 1 <;> ring
  have hRight := v26_ball_mul_const_left (a := {ql(M[N])}) hD4
  have hEraw := v26_ball_sub hLeft hRight
  have hE : v26Ball
      (2 * Real.pi ^ 2 *
          ((v26LocalM1 {N} x) ^ 2 + v21RootH {N} x * v26LocalM2 {N} x) -
        {ql(M[N])} * (v21D x) ^ 4) _ _ := by
    convert hEraw using 1 <;> ring
  have hnon : 0 ≤
      2 * Real.pi ^ 2 *
          ((v26LocalM1 {N} x) ^ 2 + v21RootH {N} x * v26LocalM2 {N} x) -
        {ql(M[N])} * (v21D x) ^ 4 := by
    apply v26_ball_nonneg hE
    norm_num {NORM_DEFS}
  rw [v26_weightXSecond_local_closed (N := {N}) hD]
  rw [le_div_iff₀ (pow_pos hDpos 4)]
  nlinarith
'''

def rec_cases(N,cells,i,low,ind="  "):
    if i==len(cells)-1:
        return ind+f"exact v26_curvature_N{N}_cell{i} {low} hU"
    cut=cells[i][1]; h=f"hcut{i}"; lo=f"hlo{i+1}"
    return (ind+f"by_cases {h} : x ≤ {ql(cut)}\n"+
            ind+f"· exact v26_curvature_N{N}_cell{i} {low} {h}\n"+
            ind+f"· have {lo} : {ql(cut)} ≤ x := le_of_not_ge {h}\n"+
            rec_cases(N,cells,i+1,lo,ind+"  "))

def curvature_aggregate(N,cells):
    L,U=J[N]
    return f'''theorem v26_curvature_N{N} {{x : ℝ}}
    (hL : {ql(L)} ≤ x) (hU : x ≤ {ql(U)}) :
    {ql(M[N])} ≤ v26WeightXSecond x := by
{rec_cases(N,cells,0,"hL","  ")}
'''

def anchor_theorems(N):
    x=A[N]; xs=ql(x); setup=ball_setup(N,x,x,False,False)
    return f'''theorem v26_anchor_weight_N{N} :
    {ql(W[N])} ≤ limitingWeight {xs} := by
  have hx89 : (89 / 100 : ℝ) < {xs} := by norm_num
  have hxcert : v17KernelCertPoint < {xs} := by
    simpa [v17KernelCertPoint] using hx89
  have hDpos : 0 < v21D {xs} := v21_D_pos (v21_A_lt_B_of_cert_lt hxcert)
{setup}
  have hH2 : v26Ball ((v21RootH {N} {xs}) ^ 2) _ _ := by
    simpa [pow_two] using v26_ball_mul hH hH
  have hD2 : v26Ball ((v21D {xs}) ^ 2) _ _ := by
    simpa [pow_two] using v26_ball_mul hDb hDb
  have hWD2 := v26_ball_mul_const_left (a := {ql(W[N])}) hD2
  have hEraw := v26_ball_sub hH2 hWD2
  have hE : v26Ball
      ((v21RootH {N} {xs}) ^ 2 - {ql(W[N])} * (v21D {xs}) ^ 2) _ _ := by
    convert hEraw using 1 <;> ring
  have hnon : 0 ≤
      (v21RootH {N} {xs}) ^ 2 - {ql(W[N])} * (v21D {xs}) ^ 2 := by
    apply v26_ball_nonneg hE
    norm_num {NORM_DEFS}
  rw [v21_limitingWeight_eq_rootH_sq_div (n := {N}) hxcert]
  rw [le_div_iff₀ (pow_pos hDpos 2)]
  nlinarith

theorem v26_anchor_deriv_N{N} :
    |v26WeightXPrime {xs} - {ql(D[N])}| ≤ (1 / 20000000 : ℝ) := by
  have hx89 : (89 / 100 : ℝ) < {xs} := by norm_num
  have hxcert : v17KernelCertPoint < {xs} := by
    simpa [v17KernelCertPoint] using hx89
  have hDpos : 0 < v21D {xs} := v21_D_pos (v21_A_lt_B_of_cert_lt hxcert)
  have hD : v21D {xs} ≠ 0 := ne_of_gt hDpos
{setup}
  have htwoPi := v26_ball_mul_const_left (a := (2 : ℝ)) hpi
  have hN1 := v26_ball_mul htwoPi hH
  have hNum := v26_ball_mul hN1 hM1
  have hD2 : v26Ball ((v21D {xs}) ^ 2) _ _ := by
    simpa [pow_two] using v26_ball_mul hDb hDb
  have hD3 : v26Ball ((v21D {xs}) ^ 3) _ _ := by
    convert v26_ball_mul hD2 hDb using 1 <;> ring
  have hLowD := v26_ball_mul_const_left
    (a := ({ql(D[N])} - (1 / 20000000 : ℝ))) hD3
  have hLowEraw := v26_ball_sub hNum hLowD
  have hLowE : v26Ball
      (2 * Real.pi * v21RootH {N} {xs} * v26LocalM1 {N} {xs} -
        ({ql(D[N])} - (1 / 20000000 : ℝ)) * (v21D {xs}) ^ 3) _ _ := by
    convert hLowEraw using 1 <;> ring
  have hlow : 0 ≤
      2 * Real.pi * v21RootH {N} {xs} * v26LocalM1 {N} {xs} -
        ({ql(D[N])} - (1 / 20000000 : ℝ)) * (v21D {xs}) ^ 3 := by
    apply v26_ball_nonneg hLowE
    norm_num {NORM_DEFS}
  have hUpD := v26_ball_mul_const_left
    (a := ({ql(D[N])} + (1 / 20000000 : ℝ))) hD3
  have hUpEraw := v26_ball_sub hUpD hNum
  have hUpE : v26Ball
      (({ql(D[N])} + (1 / 20000000 : ℝ)) * (v21D {xs}) ^ 3 -
        2 * Real.pi * v21RootH {N} {xs} * v26LocalM1 {N} {xs}) _ _ := by
    convert hUpEraw using 1 <;> ring
  have hup : 0 ≤
      ({ql(D[N])} + (1 / 20000000 : ℝ)) * (v21D {xs}) ^ 3 -
        2 * Real.pi * v21RootH {N} {xs} * v26LocalM1 {N} {xs} := by
    apply v26_ball_nonneg hUpE
    norm_num {NORM_DEFS}
  rw [v26_weightXPrime_local_closed (N := {N}) hD]
  have hden3 : 0 < (v21D {xs}) ^ 3 := pow_pos hDpos 3
  have hlofrac :
      {ql(D[N])} - (1 / 20000000 : ℝ) ≤
        2 * Real.pi * v21RootH {N} {xs} * v26LocalM1 {N} {xs} /
          (v21D {xs}) ^ 3 := by
    apply (le_div_iff₀ hden3).2
    nlinarith
  have hupfrac :
      2 * Real.pi * v21RootH {N} {xs} * v26LocalM1 {N} {xs} /
          (v21D {xs}) ^ 3 ≤
        {ql(D[N])} + (1 / 20000000 : ℝ) := by
    apply (div_le_iff₀ hden3).2
    nlinarith
  rw [abs_le]
  constructor <;> linarith
'''

def write_all(out):
    out.mkdir(parents=True,exist_ok=True); mods=[]; diag={}
    for N in range(1,11):
        cells=partitions(N); am=anchor_margins(N)
        assert min(am)>0
        diag[str(N)]={
          "cells":len(cells),
          "curvature_min_cross_margin":str(min(curvature_margin(N,l,u) for l,u in cells)),
          "anchor_weight_cross_margin":str(am[0]),
          "anchor_deriv_lower_cross_margin":str(am[1]),
          "anchor_deriv_upper_cross_margin":str(am[2])}
        mod=f"V26FinalNumericN{N}Generated"; mods.append(mod)
        txt="import HurtadoZeta23.V26FinalIntervalCore\nimport HurtadoZeta23.V26StrongConvexityLemma\nimport Mathlib.Tactic\n\nnoncomputable section\nnamespace HurtadoZeta23\n\n"
        for k,(l,u) in enumerate(cells): txt+=curvature_theorem(N,k,l,u)+"\n"
        txt+=curvature_aggregate(N,cells)+"\n"+anchor_theorems(N)+"\nend HurtadoZeta23\n"
        (out/f"{mod}.lean").write_text(txt,encoding="utf-8")
    agg="\n".join(f"import HurtadoZeta23.{m}" for m in mods)
    agg+="\n\nnamespace HurtadoZeta23\n\ntheorem v26_final_numeric_certificates_loaded : True := by trivial\n\nend HurtadoZeta23\n"
    (out/"V26FinalNumericGenerated.lean").write_text(agg,encoding="utf-8")
    man={"modules":mods,"diagnostics":diag,"files":{}}
    for p in sorted(out.glob("V26FinalNumeric*.lean")):
        b=p.read_bytes(); man["files"][p.name]={"bytes":len(b),"sha256":hashlib.sha256(b).hexdigest()}
    (out/"v26_final_numeric_manifest.json").write_text(json.dumps(man,indent=2,sort_keys=True)+"\n")
    return man

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--out-dir",required=True); ns=ap.parse_args()
    man=write_all(Path(ns.out_dir))
    print("FINAL NUMERIC EXACT GENERATION OK")
    print("curvature cells:",sum(v["cells"] for v in man["diagnostics"].values()))
    for n,d in man["diagnostics"].items(): print(n,d)

if __name__=="__main__": main()
