module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Invertible
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections

/-!
# Evaluation pairings on global sections

This leaf owns the global-sections form of the evaluation pairing between a
module sheaf and its internal-Hom dual. It is independent of a particular
trivialization or base-change argument; those hypotheses prove bijectivity in
downstream applications.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Global-sections constructions involving internal-Hom duals of module sheaves. -/
namespace GlobalSections

/-- The evaluation pairing on global sections of a module sheaf and its internal-Hom dual. -/
noncomputable def evaluationLinearMap
    (L : X.Modules) :
    ((moduleGlobalSectionsFunctor X).obj L) ⊗[globalSectionsRing X]
      ((moduleGlobalSectionsFunctor X).obj
        ((ihom L).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
          ModuleCat (globalSectionsRing X)) →ₗ[globalSectionsRing X] globalSectionsRing X :=
  TensorProduct.lift
    { toFun := fun s ↦
        { toFun := fun t ↦
            (SheafOfModules.sectionsMap
                ((ihom.ev L).app (SheafOfModules.unit X.ringCatSheaf : X.Modules))
                (tensorSection
                  (sectionFromTop L s)
                  (sectionFromTop
                    ((ihom L).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules)) t))).1
              (Opposite.op (⊤ : Opens X.carrier))
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }

/-- When the global-sections evaluation pairing is bijective, it induces the corresponding linear
equivalence. -/
noncomputable def evaluationLinearEquivOfBijective
    (L : X.Modules) (h : Function.Bijective (evaluationLinearMap L)) :
    ((moduleGlobalSectionsFunctor X).obj L) ⊗[globalSectionsRing X]
      ((moduleGlobalSectionsFunctor X).obj
        ((ihom L).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
          ModuleCat (globalSectionsRing X)) ≃ₗ[globalSectionsRing X] globalSectionsRing X :=
  LinearEquiv.ofBijective (evaluationLinearMap L) h

/-- The forward map of `evaluationLinearEquivOfBijective` is the evaluation pairing. -/
theorem evaluationLinearEquivOfBijective_toLinearMap
    (L : X.Modules) (h : Function.Bijective (evaluationLinearMap L)) :
    (evaluationLinearEquivOfBijective L h).toLinearMap = evaluationLinearMap L := sorry

end GlobalSections

end AlgebraicGeometry.RingedSpace
