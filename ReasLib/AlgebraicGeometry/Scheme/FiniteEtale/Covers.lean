/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Arrow
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale

/-!
# Finite étale arrows over a base scheme

The category of finite étale morphisms in `Over S` and its target projection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The category of finite étale morphisms of schemes over `S`. An object is a
finite étale morphism `Y ⟶ X` in `Over S`; a morphism is a commutative square
in `Over S`. -/
abbrev Covers (S : Scheme.{u}) :=
  (finiteEtaleMorphism.inverseImage (Over.forget S)).Arrow ⊤ ⊤

/-- Package a finite étale morphism of `S`-schemes as an object of `Covers S`. -/
def mk {S : Scheme.{u}} {Y X : Over S} (f : Y ⟶ X)
    (hf : finiteEtaleMorphism f.left) : Covers S :=
  MorphismProperty.Arrow.mk f hf

/-- The structure morphism of `mk f hf` is `f`. -/
theorem mk_hom {S : Scheme.{u}} {Y X : Over S} (f : Y ⟶ X)
    (hf : finiteEtaleMorphism f.left) : (mk f hf).hom = f := sorry

/-- A morphism of `S`-schemes satisfies the defining property of `Covers S` if and only if its
underlying scheme morphism is finite étale. -/
theorem mem_iff {S : Scheme.{u}} {Y X : Over S} (f : Y ⟶ X) :
    (finiteEtaleMorphism.inverseImage (Over.forget S)) f ↔
      finiteEtaleMorphism f.left := sorry

/-- The forgetful functor from finite étale arrows over `S` to `Arrow (Over S)`. -/
abbrev toArrow (S : Scheme.{u}) : Covers S ⥤ CategoryTheory.Arrow (Over S) :=
  MorphismProperty.Arrow.forget _ ⊤ ⊤

/-- The target projection sending a finite étale morphism `Y ⟶ X` over `S` to `X`. -/
abbrev p (S : Scheme.{u}) : Covers S ⥤ Over S :=
  toArrow S ⋙ CategoryTheory.Arrow.rightFunc

/-- The projection `p` sends `mk f hf` to the target `S`-scheme. -/
theorem p_obj {S : Scheme.{u}} {Y X : Over S} (f : Y ⟶ X)
    (hf : finiteEtaleMorphism f.left) : (p S).obj (mk f hf) = X := sorry

end AlgebraicGeometry.Scheme.FiniteEtale
