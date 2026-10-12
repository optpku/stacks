/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.FieldTheory.Galois.IntegralClosure.Tower

/-!
# Lemma 15.111.11

@stack 0BSX
-/

@[expose] public section

open scoped Pointwise

universe u v w z

/-
Lemma 15.111.11 (tag `0BSX`).  Let `A` be a normal domain with fraction field `K` and
let `M/L/K` be a (possibly infinite) Galois tower.  Write `C` and `B` for the integral
closures of `A` in `M` and `L`.  The ReasLib owner uses the explicit contraction
`integralClosure.Tower.under r`, induced by the canonical `towerMap`; this avoids a
pair-dependent `Algebra B C` instance while retaining the textbook meaning `B ∩ r`.
The two displayed surjectivity statements are the atomic decomposition- and inertia-group
clauses; the owner also exposes the corresponding subgroup-image equalities as companion bridges.
-/

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsGalois K L]
variable {M : Type z} [Field M] [Algebra L M] [Algebra K M] [Algebra A M]
  [IsScalarTower K L M] [IsScalarTower A K M] [IsScalarTower A L M]
  [IsGalois K M]

@[stacks 0BSX "Lemma 15.111.11 (1)"]
#check fun (r : Ideal (integralClosure A M)) [r.IsPrime] ↦
  (integralClosure.Tower.decompositionHom_surjective
      (A := A) (K := K) (L := L) (M := M) r :
    Function.Surjective
      (integralClosure.Tower.decompositionHom (A := A) (K := K) (L := L) (M := M) r))

@[stacks 0BSX "Lemma 15.111.11 (2)"]
#check fun (r : Ideal (integralClosure A M)) [r.IsPrime] ↦
  (integralClosure.Tower.inertiaHom_surjective
      (A := A) (K := K) (L := L) (M := M) r :
    Function.Surjective
      (integralClosure.Tower.inertiaHom (A := A) (K := K) (L := L) (M := M) r))

end
