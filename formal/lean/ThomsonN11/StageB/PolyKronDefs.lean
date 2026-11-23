/-!
# Thomson N = 11 Stage B — Pure `Init` Integer Data Structures & Kronecker Evaluators

Zero-Mathlib (`Init`-only) data structures and integer evaluators for `PolyKron` and
`PolyKronFast`. Keeping these definitions independent of `Mathlib` allows the certificate
data modules (`SdpCertHarmData`, `SdpCertSosData`) and all 19 parallel Kronecker slice
modules (`SdpCertSosSlice*`) to elaborate and verify in Lean's kernel with zero `Mathlib`
`.olean` import overhead (~40 MB RAM instead of ~3.5 GB per process).
-/

namespace ThomsonN11.StageB.PolyKron

def pevalZ : List Int → Int → Int
  | [], _ => 0
  | a :: as, y => a + y * pevalZ as y

def l1List (p : List Int) : Nat :=
  p.foldl (fun acc a => acc + a.natAbs) 0

def padd : List Int → List Int → List Int
  | [], q => q
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: padd as bs

def pscale (c : Int) (p : List Int) : List Int := p.map (c * ·)

def pneg (p : List Int) : List Int := p.map (- ·)

def pmul : List Int → List Int → List Int
  | [], _ => []
  | a :: as, q => padd (pscale a q) (0 :: pmul as q)

def ppow (p : List Int) : Nat → List Int
  | 0 => [1]
  | n + 1 => pmul p (ppow p n)

def chol1DPoly (cols : List (List Int)) : List Int :=
  cols.foldl (fun acc col => padd acc (pmul col col)) []

def bernSum (a b : List Int) (n : Nat) : Nat → List Nat → List Int
  | _, [] => []
  | i, β :: bs =>
    padd (pscale (β : Int) (pmul (ppow a i) (ppow b (n - i)))) (bernSum a b n (i + 1) bs)

structure BPiece where
  u1 : Int
  u2 : Nat
  w1 : Int
  w2 : Nat
  Lam : Nat
  β : List Nat

def BPiece.diff (P : List Int) (c : BPiece) : List Int :=
  padd (pscale (c.Lam : Int) P)
    (pneg (bernSum [-c.u1, (c.u2 : Int)] [c.w1, -(c.w2 : Int)] (c.β.length - 1) 0 c.β))

def BPiece.check (P : List Int) (c : BPiece) : Bool :=
  0 < c.Lam && 0 < c.u2 && 0 < c.w2 && (c.diff P).all (· == 0)

abbrev Poly3 := List (Int × Nat × Nat × Nat)

def kev3Shift (eu ev et : Nat) (p : Poly3) : Int :=
  p.foldl (fun acc x => acc + x.1 * ((Nat.shiftLeft 1 (eu * x.2.1 + ev * x.2.2.1 + et * x.2.2.2) : Nat) : Int)) 0

def kev3 (w D : Nat) (p : Poly3) : Int :=
  p.foldl (fun acc x => acc + x.1 * ((Nat.shiftLeft 1 (w * (x.2.1 + D * x.2.2.1 + D * D * x.2.2.2)) : Nat) : Int)) 0

def l1Poly3 (p : Poly3) : Nat :=
  p.foldl (fun acc x => acc + x.1.natAbs) 0

structure CholPlainBlk where
  mult : Nat
  mp : Poly3
  basis : Array Poly3
  cols : Array (List (Nat × Int))

def cholPlainKev (w D : Nat) (blk : CholPlainBlk) : Int :=
  let bvals := blk.basis.map (kev3 w D)
  let sumSq := blk.cols.foldl (fun acc col =>
    let s := col.foldl (fun a x => a + x.2 * bvals.getD x.1 0) 0
    acc + s * s) 0
  (blk.mult : Int) * kev3 w D blk.mp * sumSq

def cholPlainKevShift (eu ev et : Nat) (blk : CholPlainBlk) : Int :=
  let bvals := blk.basis.map (kev3Shift eu ev et)
  let sumSq := blk.cols.foldl (fun acc col =>
    let s := col.foldl (fun a x => a + x.2 * bvals.getD x.1 0) 0
    acc + s * s) 0
  (blk.mult : Int) * kev3Shift eu ev et blk.mp * sumSq

structure CholStdBlk where
  mp : Poly3
  e1 : Array Poly3
  e2 : Array Poly3
  cols : Array (List (Nat × Int))

def cholStdKev (w D : Nat) (blk : CholStdBlk) : Int :=
  let v1 := blk.e1.map (kev3 w D)
  let v2 := blk.e2.map (kev3 w D)
  let sumSq := blk.cols.foldl (fun acc col =>
    let s1 := col.foldl (fun a x => a + x.2 * v1.getD x.1 0) 0
    let s2 := col.foldl (fun a x => a + x.2 * v2.getD x.1 0) 0
    acc + s1 * s1 + 3 * (s2 * s2)) 0
  kev3 w D blk.mp * sumSq

def cholPlainL1 (blk : CholPlainBlk) : Nat :=
  let bl1 := blk.basis.map l1Poly3
  let sumSq := blk.cols.foldl (fun acc col =>
    let s := col.foldl (fun a x => a + x.2.natAbs * bl1.getD x.1 0) 0
    acc + s * s) 0
  blk.mult * l1Poly3 blk.mp * sumSq

def cholStdL1 (blk : CholStdBlk) : Nat :=
  let l1_1 := blk.e1.map l1Poly3
  let l1_2 := blk.e2.map l1Poly3
  let sumSq := blk.cols.foldl (fun acc col =>
    let s1 := col.foldl (fun a x => a + x.2.natAbs * l1_1.getD x.1 0) 0
    let s2 := col.foldl (fun a x => a + x.2.natAbs * l1_2.getD x.1 0) 0
    acc + (s1 * s1 + 3 * (s2 * s2))) 0
  l1Poly3 blk.mp * sumSq

def q3Z : Nat → Int → Int → Int → Int
  | 0, _, _, _ => 1
  | 1, u, v, t => t - u * v
  | k + 2, u, v, t =>
      2 * (t - u * v) * q3Z (k + 1) u v t - (1 - u * u) * (1 - v * v) * q3Z k u v t

def q3L1 : Nat → Nat
  | 0 => 1
  | 1 => 2
  | k + 2 => 4 * q3L1 (k + 1) + 4 * q3L1 k

structure CholHarmBlk where
  k : Nat
  m : Nat
  cols : Array (List (Nat × Int))

def harmColKevShift (e : Nat) (col : List (Nat × Int)) : Int :=
  col.foldl (fun acc p => acc + p.2 * ((Nat.shiftLeft 1 (e * p.1) : Nat) : Int)) 0

def harmBlkKevShift (eu ev et : Nat) (blk : CholHarmBlk) : Int :=
  let U : Int := ((Nat.shiftLeft 1 eu : Nat) : Int)
  let V : Int := ((Nat.shiftLeft 1 ev : Nat) : Int)
  let T : Int := ((Nat.shiftLeft 1 et : Nat) : Int)
  let qk := q3Z blk.k U V T
  let sumProd := blk.cols.foldl (fun acc col =>
    acc + harmColKevShift eu col * harmColKevShift ev col) 0
  qk * sumProd

def harmListKevShift (eu ev et : Nat) (blks : List CholHarmBlk) : Int :=
  blks.foldl (fun acc blk => acc + harmBlkKevShift eu ev et blk) 0

def harmBlkL1 (blk : CholHarmBlk) : Nat :=
  let sumSq := blk.cols.foldl (fun acc col =>
    let s := col.foldl (fun a p => a + p.2.natAbs) 0
    acc + s * s) 0
  q3L1 blk.k * sumSq

def harmListL1 (blks : List CholHarmBlk) : Nat :=
  blks.foldl (fun acc blk => acc + harmBlkL1 blk) 0

end ThomsonN11.StageB.PolyKron

namespace ThomsonN11.StageB.PolyKronFast

open ThomsonN11.StageB.PolyKron

inductive Trie (α : Type) where
  | empty : Trie α
  | leaf : α → Trie α
  | node : Trie α → Trie α → Trie α

def splitEO {α : Type} : List α → List α × List α
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: rest =>
    let p := splitEO rest
    (a :: p.1, b :: p.2)

def Trie.ofList : Nat → List Int → Trie Int
  | _, [] => .empty
  | _, [a] => .leaf a
  | 0, _ => .empty
  | fuel + 1, l =>
    let p := splitEO l
    .node (Trie.ofList fuel p.1) (Trie.ofList fuel p.2)

def Trie.get : Trie Int → Nat → Int
  | .empty, _ => 0
  | .leaf v, 0 => v
  | .leaf _, _ + 1 => 0
  | .node e o, n => if n % 2 == 0 then e.get (n / 2) else o.get (n / 2)

def kev2T (eu ev : Nat) (T : Int) (p : Poly3) : Int :=
  p.foldl (fun acc x =>
    acc + x.1 * T ^ x.2.2.2 * ((Nat.shiftLeft 1 (eu * x.2.1 + ev * x.2.2.1) : Nat) : Int)) 0

def kev2T_tuv (eu ev : Nat) (T : Int) (p : Poly3) : Int :=
  p.foldl (fun acc x =>
    acc + x.1 * T ^ x.2.1 * ((Nat.shiftLeft 1 (eu * x.2.2.1 + ev * x.2.2.2) : Nat) : Int)) 0

def evalPlainCols (tr : Trie Int) (cols : List (List (Nat × Int))) : Int :=
  cols.foldl (fun acc col =>
    let s := col.foldl (fun a x => a + x.2 * tr.get x.1) 0
    acc + s * s) 0

def evalStdCols (tr1 tr2 : Trie Int) (cols : List (List (Nat × Int))) : Int :=
  cols.foldl (fun acc col =>
    let s1 := col.foldl (fun a x => a + x.2 * tr1.get x.1) 0
    let s2 := col.foldl (fun a x => a + x.2 * tr2.get x.1) 0
    acc + s1 * s1 + 3 * (s2 * s2)) 0

def cholPlainKev2T (eu ev : Nat) (T : Int) (blk : CholPlainBlk) : Int :=
  let tr := Trie.ofList 8 (blk.basis.toList.map (kev2T eu ev T))
  (blk.mult : Int) * kev2T eu ev T blk.mp * evalPlainCols tr blk.cols.toList

def cholPlainKev2T_tuv (eu ev : Nat) (T : Int) (blk : CholPlainBlk) : Int :=
  let tr := Trie.ofList 8 (blk.basis.toList.map (kev2T_tuv eu ev T))
  (blk.mult : Int) * kev2T_tuv eu ev T blk.mp * evalPlainCols tr blk.cols.toList

def cholStdKev2T (eu ev : Nat) (T : Int) (blk : CholStdBlk) : Int :=
  let tr1 := Trie.ofList 8 (blk.e1.toList.map (kev2T eu ev T))
  let tr2 := Trie.ofList 8 (blk.e2.toList.map (kev2T eu ev T))
  kev2T eu ev T blk.mp * evalStdCols tr1 tr2 blk.cols.toList

def harmColEvZ (x : Int) (col : List (Nat × Int)) : Int :=
  col.foldl (fun a p => a + p.2 * x ^ p.1) 0

def harmBlkKev2T (eu ev : Nat) (T : Int) (blk : CholHarmBlk) : Int :=
  let U : Int := ((Nat.shiftLeft 1 eu : Nat) : Int)
  let V : Int := ((Nat.shiftLeft 1 ev : Nat) : Int)
  q3Z blk.k U V T * blk.cols.foldl (fun acc col => acc + harmColKevShift eu col * harmColKevShift ev col) 0

def harmListKev2T (eu ev : Nat) (T : Int) (blks : List CholHarmBlk) : Int :=
  blks.foldl (fun acc blk => acc + harmBlkKev2T eu ev T blk) 0

def harmBlkKev2T_utv (eu ev : Nat) (T : Int) (blk : CholHarmBlk) : Int :=
  let U : Int := ((Nat.shiftLeft 1 eu : Nat) : Int)
  let V : Int := ((Nat.shiftLeft 1 ev : Nat) : Int)
  q3Z blk.k U T V * blk.cols.foldl (fun acc col => acc + harmColKevShift eu col * harmColEvZ T col) 0

def harmListKev2T_utv (eu ev : Nat) (T : Int) (blks : List CholHarmBlk) : Int :=
  blks.foldl (fun acc blk => acc + harmBlkKev2T_utv eu ev T blk) 0

def harmBlkEvZ (U V T : Int) (blk : CholHarmBlk) : Int :=
  q3Z blk.k U V T * blk.cols.foldl (fun acc col => acc + harmColEvZ U col * harmColEvZ V col) 0

def harmListEvZ (U V T : Int) (blks : List CholHarmBlk) : Int :=
  blks.foldl (fun acc blk => acc + harmBlkEvZ U V T blk) 0

def cholPlainL1Fast (B : Nat) (blk : CholPlainBlk) : Nat :=
  blk.mult * l1Poly3 blk.mp * (B * B * blk.cols.toList.foldl (fun acc col =>
    let s := col.foldl (fun a x => a + x.2.natAbs) 0
    acc + s * s) 0)

def cholStdL1Fast (B1 B2 : Nat) (blk : CholStdBlk) : Nat :=
  l1Poly3 blk.mp * ((B1 * B1 + 3 * (B2 * B2)) * blk.cols.toList.foldl (fun acc col =>
    let s := col.foldl (fun a x => a + x.2.natAbs) 0
    acc + s * s) 0)

end ThomsonN11.StageB.PolyKronFast
