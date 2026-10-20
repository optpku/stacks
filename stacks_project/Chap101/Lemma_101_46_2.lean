/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap101.Definition_101_10_1_Integral
public import stacks_project.Chap101.Lemma_101_46_2_Normalization

/-!
# Absolute normalization morphisms of algebraic stacks

Lemma 101.46.2 constructs, for every algebraic stack satisfying the equivalent
conditions of Lemma 101.46.1, a canonical integral absolute normalization
morphism `ν : X^ν ⟶ X` whose 2-fibre product against every smooth morphism from
a scheme is the normalization of that scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.46.2 (1). Let `X` be an algebraic stack satisfying the equivalent
conditions of Lemma 101.46.1. Then the canonical 1-morphism
`normalizationTo X : normalization X ⟶ X` of algebraic stacks is integral. -/
@[stacks 0GMJ]
instance instIsIntegralHom_normalizationTo {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    IsIntegralHom (normalizationTo X) :=
  sorry

/-- Lemma 101.46.2 (2). Let `X` be an algebraic stack satisfying the equivalent
conditions of Lemma 101.46.1. Then for every scheme `U` and every smooth
morphism `p : U ⟶ X`, the 2-fibre product `normalization X ×_X U` is equivalent
over `U` to the normalization of `U`. -/
@[stacks 0GMJ]
theorem exists_pullbackEquivalence_of_smooth {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : Over S) (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p] :
    ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} (normalizationTo X) p ≌
        GroupoidsOver.slice (smoothSliceOverNormalization U p),
      Nonempty
        (e.hom ≫ sliceNormalizationHom U p ≅
          TwoFibreProduct.snd.{u + 1, u, u + 1, u} (normalizationTo X) p) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
