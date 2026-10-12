/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.PurelyInseparable.HigherTrace
import StacksCheckRecall

open Polynomial
open scoped TensorProduct
universe u

namespace PurelyInseparableTrace.Higher

/- Lemma 54.2.2 (1): the canonical higher trace. -/
@[stacks 0AX5]
#check (PurelyInseparableTrace.Higher.traceOfEquiv_wedge_rootPowD :
  ∀ (p : ℕ) (hp : p.Prime)
(Λ R S : Type u) [CommRing Λ] [CommRing R] [CommRing S]
[Algebra (ZMod p) Λ] [Algebra (ZMod p) R] [Algebra Λ R]
[IsScalarTower (ZMod p) Λ R] [Nontrivial R]
[Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]
(a : R) (e : S ≃ₐ[R] AdjoinRoot (X ^ p - C a)),
  ∀ (t : ℕ)
    (η : KaehlerDifferential.DeRham.Form Λ R t) (i : Fin p),
    traceOfEquiv p hp a e (t + 1)
        (KaehlerDifferential.DeRham.formWedge Λ S t 1
          (pullback t η ⊗ₜ
            KaehlerDifferential.DeRham.basic Λ S 1
              ((e.symm (AdjoinRoot.root (X ^ p - C a))) ^ (i : ℕ))
              (fun _ ↦ e.symm (AdjoinRoot.root (X ^ p - C a))))) =
      if (i : ℕ) = p - 1 then
        KaehlerDifferential.DeRham.formWedge Λ R t 1
          (η ⊗ₜ KaehlerDifferential.DeRham.basic Λ R 1 1 (fun _ ↦ a))
      else 0)

/- Lemma 54.2.2 (2): the canonical higher trace. -/
@[stacks 0AX5]
#check (PurelyInseparableTrace.Higher.traceOfEquiv_baseChange :
  ∀ (p : ℕ) (hp : p.Prime)
(Λ R S : Type u) [CommRing Λ] [CommRing R] [CommRing S]
[Algebra (ZMod p) Λ] [Algebra (ZMod p) R] [Algebra Λ R]
[IsScalarTower (ZMod p) Λ R] [Nontrivial R]
[Algebra R S] [Algebra Λ S] [IsScalarTower Λ R S]
(a : R) (e : S ≃ₐ[R] AdjoinRoot (X ^ p - C a)),
  ∀ (t : ℕ)
    (s : S) (η : KaehlerDifferential.DeRham.Form Λ R (t + 1)),
    traceOfEquiv p hp a e (t + 1)
      (s • pullback (t + 1) η) = 0)

end PurelyInseparableTrace.Higher
