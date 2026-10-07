module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.MooreComparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Dold--Kan equivalence for the canonical normalized quotient

The canonical normalized quotient is compared directly with transported Moore cochains, so this
equivalence is independent of the source-facing degreewise span and quotient presentations.

@stack 019I
-/

@[expose] public section

open CategoryTheory AlgebraicTopology

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject.DoldKan.degenerate.normalized

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The canonical normalized image quotient realizes the cosimplicial Dold--Kan equivalence. -/
@[stacks 019I "canonical normalized image quotient equivalence"]
noncomputable def equivalence : CosimplicialObject A ≌ CochainComplex A ℕ :=
  (normalizedMooreCochainComplex.equivalence (A := A)).changeFunctor
    (moore.natIso (A := A))

/-- The canonical normalized image quotient functor is an equivalence. -/
@[instance, stacks 019I "canonical normalized image quotient is an equivalence"]
theorem functor.isEquivalence :
    (functor (A := A)).IsEquivalence := sorry

end CategoryTheory.CosimplicialObject.DoldKan.degenerate.normalized
