/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap69.Lemma_69_6_1_Comparison
public import stacks_project.Chap69.Lemma_69_6_1_ExtensionByZero

/-!
# Lemma 69.6.1

Canonical isomorphisms
`f1_! underline(ℤ) ⊗_ℤ f2_! underline(ℤ) ⟶ f12_! underline(ℤ)`
and
`(f1 ⨿ f2)_! underline(ℤ) ⟶ f1_! underline(ℤ) ⊕ f2_! underline(ℤ)`
for étale morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X U1 U2 : AlgebraicSpace S}

/-- Lemma 69.6.1 (1): for étale morphisms `f1 : U1 ⟶ X` and `f2 : U2 ⟶ X` of algebraic
spaces over a scheme `S`, the Hom-pairing
`1_φ1 ⊗ 1_φ2 ↦ 1_{φ1 × φ2}` induces an isomorphism
`f1_! underline(ℤ) ⊗_ℤ f2_! underline(ℤ) ⟶ (pullback.fst f1 f2 ≫ f1)_! underline(ℤ)`. -/
@[stacks 0722, instance]
instance ExtensionByZeroInteger.tensorComparison_isIso (f1 : U1 ⟶ X) (f2 : U2 ⟶ X)
    [HasPullback f1 f2] [Etale f1] [Etale f2] :
    IsIso (ExtensionByZeroInteger.tensorComparison f1 f2) :=
  sorry

/-- Lemma 69.6.1 (2): for étale morphisms `f1 : U1 ⟶ X` and `f2 : U2 ⟶ X` of algebraic
spaces over a scheme `S`, coproduct inclusions induce an isomorphism
`(f1 ⨿ f2)_! underline(ℤ) ⟶ f1_! underline(ℤ) ⊕ f2_! underline(ℤ)`. -/
@[stacks 0722, instance]
instance ExtensionByZeroInteger.coprodComparison_isIso (f1 : U1 ⟶ X) (f2 : U2 ⟶ X)
    [Etale f1] [Etale f2] :
    IsIso (ExtensionByZeroInteger.coprodComparison f1 f2) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
