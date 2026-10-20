/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward

/-!
# Pullback of scheme-module cohomology

The module pullback–pushforward unit and the additive-sheaf direct-image comparison
give pullback of cohomology classes for schemes over an affine base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Direct image of a scheme module has the topological pushforward as its underlying
additive sheaf. -/
def pushforwardToSheaf {X Y : Scheme.{u}} (π : Y ⟶ X) (G : Y.Modules) :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj ((pushforward π).obj G) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} π.base).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj G) :=
  𝟙 _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- The cohomology map induced by the module adjunction unit `L ⟶ π_* π^* L`
for a scheme over `Spec R`. -/
def cohomologyMapOfUnit (f : X ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ X)
    (L : X.Modules) (p : ℕ) :
    cohomology f L p ⟶
      cohomology f ((Modules.pushforward π).obj ((Modules.pullback π).obj L)) p :=
  (cohomologyFunctor f p).map ((Modules.pullbackPushforwardAdjunction π).unit.app L)

/-- The unit-induced cohomology map is the image of the adjunction unit
under the cohomology functor. -/
theorem cohomologyMapOfUnit_eq (f : X ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ X)
    (L : X.Modules) (p : ℕ) :
    cohomologyMapOfUnit f π L p =
      (cohomologyFunctor f p).map ((Modules.pullbackPushforwardAdjunction π).unit.app L) := sorry

/-- Pullback of a scheme-module cohomology class is induced by the module adjunction
unit followed by the additive-sheaf direct-image comparison. -/
def cohomologyPullback (f : X ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ X)
    (L : X.Modules) (p : ℕ) (ξ : cohomology f L p) :
    cohomology (π ≫ f) ((Modules.pullback π).obj L) p :=
  let pushed := (cohomologyMapOfUnit f π L p).hom ξ
  let forgotten :=
    (eqToHom (cohomologyForget_obj_eq f
      ((Modules.pushforward π).obj ((Modules.pullback π).obj L)) p)).hom pushed
  let compared :=
    (CategoryTheory.Sheaf.cohomologyMap
      (Modules.pushforwardToSheaf π ((Modules.pullback π).obj L)) p ⊤).hom forgotten
  let onY :=
    (CategoryTheory.Sheaf.pushforwardCohomologyMap π.base
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Modules.pullback π).obj L)) p ⊤).hom
      compared
  (eqToHom (cohomologyForget_obj_eq (π ≫ f) ((Modules.pullback π).obj L) p).symm).hom onY

/-- Pullback applies the unit-induced map, forgets scalars, compares direct-image
cohomology, and restores the affine-base scalar action. -/
theorem cohomologyPullback_apply (f : X ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ X)
    (L : X.Modules) (p : ℕ) (ξ : cohomology f L p) :
    cohomologyPullback f π L p ξ =
      (eqToHom (cohomologyForget_obj_eq (π ≫ f) ((Modules.pullback π).obj L) p).symm).hom
        ((CategoryTheory.Sheaf.pushforwardCohomologyMap π.base
          ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Modules.pullback π).obj L)) p ⊤).hom
          ((CategoryTheory.Sheaf.cohomologyMap
            (Modules.pushforwardToSheaf π ((Modules.pullback π).obj L)) p ⊤).hom
            ((eqToHom (cohomologyForget_obj_eq f
              ((Modules.pushforward π).obj ((Modules.pullback π).obj L)) p)).hom
              ((cohomologyMapOfUnit f π L p).hom ξ)))) := sorry

end AlgebraicGeometry.Scheme.Hom
