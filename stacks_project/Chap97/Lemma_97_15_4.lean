/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.LciSurjective
public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.LciFormallySmooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 97.15.4: The positive-degree LCI Hilbert coproduct of a flat,
surjective, locally finitely presented morphism representable by algebraic spaces
is surjective on objects. -/
@[stacks 06DA] #check (AlgebraicGeometry.FiniteHilbertStack.lciCoproduct.forgetToY.surjectiveOnObjects :
  ∀ {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.Surjective (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)],
    Groupoids.Hom.SurjectiveOnObjects
      (asGroupoidsOverMor (lciCoproduct.forgetToY F)))

#check (AlgebraicGeometry.FiniteHilbertStack.exists_lciObj_over_field :
  ∀ {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.Surjective (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)]
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S)
    (y : GroupoidsOver.slice (Over.mk σ) ⟶ asGroupoidsOver 𝒴),
    ∃ (d : ℕ) (_ : 0 < d) (ξ : Obj (asGroupoidsOverMor F) d)
      (hU : ξ.U = Over.mk σ),
      Obj.IsLci (asGroupoidsOverMor F) ξ ∧
        Nonempty
          (YonedaSlice.representative ξ.y ≅
            slice.pullback (eqToHom hU) y))
