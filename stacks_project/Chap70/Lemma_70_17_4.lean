/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap70.Lemma_70_17_4_Quotient

/-!
# Maximal nonscheme quotient ideals

A quasi-compact quasi-separated algebraic space over an affine scheme that is
not a scheme admits an ideal of the coordinate ring which is maximal among
ideals whose base change is not a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 70.17.4: Let `φ : X ⟶ Spec (CommRingCat.of A)` be a quasi-compact and
quasi-separated morphism from an algebraic space to an affine scheme, identified
with `toBase X`. If `X` is not a scheme, then there exists an ideal `I` of `A`
such that `baseChangeQuotient X I` is not a scheme, but `baseChangeQuotient X J`
is a scheme whenever `I < J`. -/
@[stacks 0B81]
theorem exists_isMaximalNonschemeIdeal {A : Type u} [CommRing A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    [IsQuasiCompact X] [IsQuasiSeparated X] (hX : ¬ IsScheme X) :
    ∃ I : Ideal A, IsMaximalNonschemeIdeal X I :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
