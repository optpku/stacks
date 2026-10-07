module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe uC vC uD vD w

namespace RingedSite.Cocontinuous.moduleLowerShriek

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

open SheafOfModules.Localization

/-- The lower-shriek Hom equivalence evaluated on the localized unit module. -/
@[stacks 07AC "underived generator Hom equivalence"]
noncomputable def structureModuleHomEquiv
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) (U : C)
    [HasLowerShriek.{w}
      (inverseImageRingSheaf (J := J) (K := K) f R)]
    [HasLowerShriek.{w} R]
    (M : SheafOfModules.{w} R) :
    ((RingedSite.Cocontinuous.moduleLowerShriek (J := J) (K := K) f R).obj
      (structureModule (inverseImageRingSheaf (J := J) (K := K) f R) U) ⟶ M) ≃
      (sectionsAt R (f.obj U)).obj M :=
  (RingedSite.Cocontinuous.moduleLowerShriek.homEquiv
      (J := J) (K := K) f R _ M).trans
    (SheafOfModules.Localization.structureModuleHomEquiv
      (inverseImageRingSheaf (J := J) (K := K) f R) U
      ((RingedSite.Cocontinuous.moduleInverseImage
        (J := J) (K := K) f R).obj M))

/-- The generator Hom equivalence is natural in the target module. -/
@[stacks 07AC "underived generator naturality"]
theorem structureModuleHomEquiv_comp
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) (U : C)
    [HasLowerShriek.{w}
      (inverseImageRingSheaf (J := J) (K := K) f R)]
    [HasLowerShriek.{w} R]
    {M N : SheafOfModules.{w} R}
    (a : (RingedSite.Cocontinuous.moduleLowerShriek (J := J) (K := K) f R).obj
      (structureModule (inverseImageRingSheaf (J := J) (K := K) f R) U) ⟶ M)
    (g : M ⟶ N) :
    structureModuleHomEquiv f R U N (a ≫ g) =
      (sectionsAt R (f.obj U)).map g (structureModuleHomEquiv f R U M a) := sorry

/-- The continuous-presentation lower-shriek sends the localized unit module to a
structure module on the target site. -/
@[stacks 07AC "generator corepresentability"]
noncomputable def structureModuleCorepresentable
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) (U : C)
    [HasLowerShriek.{w}
      (inverseImageRingSheaf (J := J) (K := K) f R)]
    [HasLowerShriek.{w} R] :
    (sectionsAt R (f.obj U)).CorepresentableBy
      ((RingedSite.Cocontinuous.moduleLowerShriek (J := J) (K := K) f R).obj
        (structureModule (inverseImageRingSheaf (J := J) (K := K) f R) U)) where
  homEquiv := fun {M} ↦ structureModuleHomEquiv f R U M
  homEquiv_comp := fun g a ↦ structureModuleHomEquiv_comp f R U a g

/-- The canonical underived generator isomorphism for lower-shriek. -/
@[stacks 07AC "underived generator isomorphism"]
noncomputable def structureModuleIso
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) (U : C)
    [HasLowerShriek.{w}
      (inverseImageRingSheaf (J := J) (K := K) f R)]
    [HasLowerShriek.{w} R] :
    (RingedSite.Cocontinuous.moduleLowerShriek (J := J) (K := K) f R).obj
        (structureModule (inverseImageRingSheaf (J := J) (K := K) f R) U) ≅
      structureModule R (f.obj U) :=
  (structureModuleCorepresentable f R U).uniqueUpToIso
    (SheafOfModules.Localization.structureModuleCorepresentable R (f.obj U))

end RingedSite.Cocontinuous.moduleLowerShriek
