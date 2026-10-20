/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap87.Lemma_87_25_2_Surjective

/-!
# Surjectivity of representable morphisms of formal algebraic spaces

A morphism of formal algebraic spaces representable by algebraic spaces is
surjective in the Bootstrap 80.4.1 sense if and only if the induced map of
reductions is a surjective morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 87.12.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S` which is representable by algebraic spaces.
Then `f` is surjective in the sense of Bootstrap, Definition 80.4.1 if and
only if `mapReduction f : reduction X ⟶ reduction Y` is a surjective morphism
of algebraic spaces. -/
@[stacks 0GB8]
theorem has_surjective_iff_mapReduction {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] {f : X ⟶ Y}
    (hf : AlgebraicSpace.representableByAlgebraicSpaces f) :
    (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
        AlgebraicSpace.Surjective (hf.pullbackHom ξ)) ↔
      AlgebraicSpace.Surjective (mapReduction f) :=
  sorry

/-- If the induced map of reductions of a representable morphism of formal
algebraic spaces is a surjective morphism of algebraic spaces, then every
scheme Yoneda pullback of the morphism is surjective. -/
theorem has_surjective_of_mapReduction {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] {f : X ⟶ Y}
    (hf : AlgebraicSpace.representableByAlgebraicSpaces f)
    (h : AlgebraicSpace.Surjective (mapReduction f)) :
    ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Surjective (hf.pullbackHom ξ) :=
  sorry

/-- If a morphism of formal algebraic spaces representable by algebraic spaces
is surjective in the sense of Bootstrap, Definition 80.4.1, then the induced
map of reductions is a surjective morphism of algebraic spaces. -/
theorem mapReduction_surjective_of_has {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] {f : X ⟶ Y}
    (hf : AlgebraicSpace.representableByAlgebraicSpaces f)
    (h : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Surjective (hf.pullbackHom ξ)) :
    AlgebraicSpace.Surjective (mapReduction f) :=
  sorry

namespace Surjective

/-- A representable morphism of formal algebraic spaces is surjective in the
sense of Definition 87.25.1 if and only if every scheme Yoneda pullback is a
surjective morphism of algebraic spaces. -/
theorem iff_has {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] {f : X ⟶ Y}
    (hf : AlgebraicSpace.representableByAlgebraicSpaces f) :
    Surjective f ↔
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
        AlgebraicSpace.Surjective (hf.pullbackHom ξ) :=
  sorry

end Surjective

end AlgebraicGeometry.FormalAlgebraicSpace
