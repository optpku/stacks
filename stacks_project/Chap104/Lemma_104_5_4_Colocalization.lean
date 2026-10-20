/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import stacks_project.Chap104.Lemma_104_5_3_Comparison

/-!
# Colocalization of `D_{LQCoh^{fbc}}(𝒪_X)` along the flat-fppf morphism

For an algebraic stack `X`, the restricted adjunction `Lg_! ⊣ g^*` of
Lemma 104.5.3 along the flat-fppf morphism of Lemma 103.14.2 supplies a
canonical functor `E ↦ Lg_! g^* E` on `D_{LQCoh^{fbc}}(𝒪_X)`. Completing
the counit to a distinguished triangle yields a parasitic cone, and
`Lg_! g^* E` is left-orthogonal to `D_{Parasitic ∩ LQCoh^{fbc}}(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbc

variable {S : Scheme.{u}}

/-- The canonical colocalization functor `E ↦ Lg_! g^* E` on
`D_{LQCoh^{fbc}}(𝒪_X)`, along the flat-fppf morphism of Lemma 103.14.2. -/
abbrev colocalize (X : GroupoidsOver S) [AlgebraicStack X] :
    DerivedLQCohFbc X ⥤ DerivedLQCohFbc X :=
  flatFppfInverseImageDerivedLQCohFbc X ⋙ flatFppfLowerShriekDerivedQCoh X

/-- `colocalize` is the composite of restricted derived `g^*` with restricted
derived `Lg_!`. -/
theorem colocalize_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    colocalize X =
      flatFppfInverseImageDerivedLQCohFbc X ⋙ flatFppfLowerShriekDerivedQCoh X :=
  sorry

/-- The adjunction counit `Lg_! g^* E ⟶ E` of the restricted flat-fppf
adjunction on `D_{LQCoh^{fbc}}(𝒪_X)`. -/
abbrev colocalizeCounit (X : GroupoidsOver S) [AlgebraicStack X] :
    colocalize X ⟶ 𝟭 (DerivedLQCohFbc X) :=
  (flatFppfLowerShriekDerivedQCoh.adjunction X).counit

/-- `colocalizeCounit` is the counit of `flatFppfLowerShriekDerivedQCoh.adjunction`. -/
theorem colocalizeCounit_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    colocalizeCounit X = (flatFppfLowerShriekDerivedQCoh.adjunction X).counit :=
  sorry

/-- The counit `Lg_! g^* E ⟶ E` completes to a distinguished triangle in
`D_{LQCoh^{fbc}}(𝒪_X)` whose third vertex has parasitic cohomology. -/
theorem exists_colocalizationTriangle (X : GroupoidsOver S) [AlgebraicStack X]
    (E : DerivedLQCohFbc X) :
    ∃ (P : DerivedLQCohFbc X) (f : E ⟶ P)
      (δ : P ⟶ ((colocalize X).obj E)⟦(1 : ℤ)⟧),
      Triangle.mk ((colocalizeCounit X).app E) f δ ∈ distTriang (DerivedLQCohFbc X) ∧
        derivedParasitic X P :=
  sorry

/-- `Lg_! g^* E` is left-orthogonal in `D(𝒪_X)` to objects with cohomology in
`Parasitic ∩ LQCoh^{fbc}`. -/
theorem colocalize_hom_eq_zero (X : GroupoidsOver S) [AlgebraicStack X]
    (E : DerivedLQCohFbc X) :
    (DerivedCategory.cohomologyIn (FppfModules.parasiticLQCohFbc X)).leftOrthogonal
      ((inclusion X).obj ((colocalize X).obj E)) :=
  sorry

/-- `Lg_! g^* E` is left-orthogonal to `derivedParasitic` in
`D_{LQCoh^{fbc}}(𝒪_X)`. -/
theorem colocalize_leftOrthogonal (X : GroupoidsOver S) [AlgebraicStack X]
    (E : DerivedLQCohFbc X) :
    (derivedParasitic X).leftOrthogonal ((colocalize X).obj E) :=
  sorry

/-- Distinguished parasitic completions of the colocalization counit are unique
up to a unique isomorphism of triangles inducing the identity on `E`. -/
theorem colocalizationTriangle_unique {X : GroupoidsOver S} [AlgebraicStack X]
    {E P P' : DerivedLQCohFbc X}
    {f : E ⟶ P} {δ : P ⟶ ((colocalize X).obj E)⟦(1 : ℤ)⟧}
    {f' : E ⟶ P'} {δ' : P' ⟶ ((colocalize X).obj E)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk ((colocalizeCounit X).app E) f δ ∈
      distTriang (DerivedLQCohFbc X))
    (hT' : Triangle.mk ((colocalizeCounit X).app E) f' δ' ∈
      distTriang (DerivedLQCohFbc X))
    (hP : derivedParasitic X P) (hP' : derivedParasitic X P') :
    ∃! e : Triangle.mk ((colocalizeCounit X).app E) f δ ≅
        Triangle.mk ((colocalizeCounit X).app E) f' δ',
      e.hom.hom₂ = 𝟙 E :=
  sorry

end AlgebraicGeometry.AlgebraicStack.DerivedLQCohFbc
