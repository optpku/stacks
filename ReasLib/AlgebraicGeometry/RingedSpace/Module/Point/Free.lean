module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Point
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Tactic.CrossRefAttribute

/-!
# Free module sheaves on a ringed point

The equivalence between modules and module sheaves on a ringed point identifies the ordinary free
module on `I` with the free module sheaf on `I`. The two comparison morphisms are built from the
respective free universal properties.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedPoint.Module

variable (R : Type u) [CommRing R]

/-- The carrier of the inverse point-module functor is the carrier of the module on the top open.
This is an additive-carrier bridge for the scalar-transport equivalence. -/
noncomputable def topSectionsCarrierEquiv (G : (RingedPoint.of R).Modules) :
    ((equivalence R).inverse.obj G : Type u) ≃
      (G.val.obj (Opposite.op
        (⊤ : TopologicalSpace.Opens RingedPoint.carrier)) : Type u) :=
  Equiv.refl _

/-- The morphism from the point sheaf associated to the ordinary free module to the free module
sheaf, classified by the tautological free-sheaf sections. -/
noncomputable def pointFreeToFree (I : Type u) :
    (functor R).obj ((ModuleCat.free R).obj I) ⟶
      (SheafOfModules.free I : (RingedPoint.of R).Modules) :=
  ((equivalence R).toAdjunction.homEquiv ((ModuleCat.free R).obj I)
    (SheafOfModules.free I)).symm
      ((ModuleCat.freeHomEquiv (R := R) (X := I)
        (M := (equivalence R).inverse.obj (SheafOfModules.free I))).symm
          (↾(fun i ↦ (topSectionsCarrierEquiv R (SheafOfModules.free I)).symm
            (RingedSpace.sectionsEquivTop (SheafOfModules.free I)
              (SheafOfModules.freeSection i)))))

/-- The morphism from the free module sheaf to the point sheaf associated to the ordinary free
module, classified by the ordinary free basis on the top open. -/
noncomputable def freeToPointFree (I : Type u) :
    (SheafOfModules.free I : (RingedPoint.of R).Modules) ⟶
      (functor R).obj ((ModuleCat.free R).obj I) :=
  ((functor R).obj ((ModuleCat.free R).obj I)).freeHomEquiv.symm (fun i ↦
    RingedSpace.sectionFromTop ((functor R).obj ((ModuleCat.free R).obj I))
      ((topValueIso R ((ModuleCat.free R).obj I)).inv (ModuleCat.freeMk i)))

/-- The two free comparison morphisms compose to the identity on the associated point sheaf. -/
theorem pointFreeToFree_comp_freeToPointFree (I : Type u) :
    pointFreeToFree R I ≫ freeToPointFree R I =
      𝟙 ((functor R).obj ((ModuleCat.free R).obj I)) := sorry

/-- The two free comparison morphisms compose to the identity on the free module sheaf. -/
theorem freeToPointFree_comp_pointFreeToFree (I : Type u) :
    freeToPointFree R I ≫ pointFreeToFree R I =
      𝟙 (SheafOfModules.free I : (RingedPoint.of R).Modules) := sorry

/-- The ordinary free `R`-module on `I`, viewed as a module sheaf on the ringed point, is
canonically isomorphic to the free module sheaf on `I`. -/
@[stacks 01BH "free modules on a ringed point"]
noncomputable def freeIso (I : Type u) :
    (functor R).obj ((ModuleCat.free R).obj I) ≅
      (SheafOfModules.free I : (RingedPoint.of R).Modules) where
  hom := pointFreeToFree R I
  inv := freeToPointFree R I
  hom_inv_id := pointFreeToFree_comp_freeToPointFree R I
  inv_hom_id := freeToPointFree_comp_pointFreeToFree R I

end AlgebraicGeometry.RingedPoint.Module
