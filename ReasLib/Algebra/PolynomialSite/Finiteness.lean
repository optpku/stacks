/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.PolynomialSite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Point

/-!
# Finite cohomology of derived lower shriek on the polynomial site

Over a Noetherian base and a finite-type target algebra, finiteness of a module-valued
presheaf on finite-type polynomial augmentations implies finiteness of every cohomology
module of its derived lower shriek.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Algebra.PolynomialSite
open CommAlgCat.Over.Polynomial (ofMvPolynomial)
open scoped CategoryTheory

universe u q q'

namespace Algebra.PolynomialSite

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [Algebra.FiniteType A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/-- Over a Noetherian base and a finite-type target algebra, a module-valued presheaf
that is finite on every finite-type polynomial augmentation has finite cohomology
modules after derived lower shriek. -/
theorem lowerShriek_homology_finite
    (F : (PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (h_eval : ∀ (Y : (PolynomialSite A B)ᵒᵖ),
      Algebra.FiniteType A Y.unop.unop.obj.left → Module.Finite B (F.obj Y))
    (i : ℤ) :
    Module.Finite B
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
        (((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
            (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj F)) :=
  sorry

/-- Over a Noetherian base and a finite-type target algebra, if a presheaf takes finite
module values on every augmentation `α : MvPolynomial ι A →ₐ[A] B` with `ι` finite,
then every cohomology module of its derived lower shriek is finite over `B`. -/
theorem lowerShriek_homology_finite_of_mvPolynomial
    (F : (PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (h_eval : ∀ (ι : Type u) [Finite ι] (α : MvPolynomial ι A →ₐ[A] B),
      Module.Finite B (F.obj (op (op (ofMvPolynomial A B ι α)))))
    (i : ℤ) :
    Module.Finite B
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
        (((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
            (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj F)) :=
  sorry

end Algebra.PolynomialSite
