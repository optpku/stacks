/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek.Localization
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard
  RingedSite.Cocontinuous.moduleLowerShriek.additive

open CategoryTheory
open ComplexShape

noncomputable section

universe z uC vC uD vD w

namespace RingedSite.Cocontinuous.moduleLowerShriek

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

open SheafOfModules.Localization

/-- The homotopy-to-derived lower-shriek presentation. -/
@[stacks 07AC "derived lower-shriek presentation"]
noncomputable abbrev toDerived
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) [UnivLE.{max uD vD, z}] :
    RingedSite.Hom.ModuleHomotopy.{z}
        (moduleInverseImage.source (J := J) (K := K) f R) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (moduleInverseImage.target (K := K) R) :=
  (RingedSite.Cocontinuous.moduleLowerShriek
      (J := J) (K := K) f R).mapHomotopyCategory (up ℤ) ⋙
    RingedSite.Hom.moduleLocalization
      (moduleInverseImage.target (K := K) R)

/-- The total-derived lower-shriek presentation is defined at every source object. -/
@[stacks 07AC "pointwise derived lower-shriek existence"]
noncomputable instance toDerived.everywhereDefined
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}] :
    Functor.LeftDerived.EverywhereDefined
      (toDerived (J := J) (K := K) f R)
      (RingedSite.Hom.ModuleQis
        (moduleInverseImage.source (J := J) (K := K) f R)) := sorry

namespace toDerived

/-- Existence of the total left-derived lower-shriek functor in a continuous presentation. -/
@[stacks 07AC "derived lower-shriek existence", instance]
theorem hasLeftDerived
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}] :
    Functor.HasLeftDerivedFunctor
      (toDerived (J := J) (K := K) f R)
      (RingedSite.Hom.ModuleQis.{z}
        (moduleInverseImage.source (J := J) (K := K) f R)) := sorry

end toDerived

/-- The total left-derived lower-shriek functor. -/
@[stacks 07AC "derived lower shriek"]
noncomputable abbrev derived
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}] :
    RingedSite.Hom.ModuleDerived.{z}
        (moduleInverseImage.source (J := J) (K := K) f R) ⥤
      RingedSite.Hom.ModuleDerived.{z}
        (moduleInverseImage.target (K := K) R) :=
  Functor.totalLeftDerived
    (toDerived (J := J) (K := K) f R)
    (RingedSite.Hom.moduleLocalization
      (moduleInverseImage.source (J := J) (K := K) f R))
    (RingedSite.Hom.ModuleQis.{z}
      (moduleInverseImage.source (J := J) (K := K) f R))

namespace derived

/-- The canonical certificate that the homotopy lower-shriek/inverse-image adjunction descends. -/
@[stacks 07AC "derived adjunction certificate", instance]
theorem hasPair
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}] :
    CategoryTheory.Adjunction.TotalDerived.HasPair
      (G := (RingedSite.Cocontinuous.moduleLowerShriek
        (J := J) (K := K) f R).mapHomotopyCategory (up ℤ))
      (F := (RingedSite.Cocontinuous.moduleInverseImage
        (J := J) (K := K) f R).mapHomotopyCategory (up ℤ))
      (RingedSite.Hom.ModuleQis.{z}
        (moduleInverseImage.source (J := J) (K := K) f R))
      (RingedSite.Hom.ModuleQis.{z}
        (moduleInverseImage.target (K := K) R))
      (L1 := RingedSite.Hom.moduleLocalization
        (moduleInverseImage.source (J := J) (K := K) f R))
      (L2 := RingedSite.Hom.moduleLocalization
        (moduleInverseImage.target (K := K) R)) := sorry

/-- The total-derived lower-shriek/inverse-image adjunction used to construct the canonical
exact-derived adjunction. -/
@[stacks 07AC "total-derived adjunction"]
noncomputable def totalAdjunction
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}] :
    moduleLowerShriek.derived (J := J) (K := K) f R ⊣
      moduleInverseImage.totalDerived (J := J) (K := K) f R :=
  CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction
      (moduleLowerShriek.adjunction (J := J) (K := K) f R))
    (RingedSite.Hom.ModuleQis.{z}
      (moduleInverseImage.source (J := J) (K := K) f R))
    (RingedSite.Hom.ModuleQis.{z}
      (moduleInverseImage.target (K := K) R))

/-- The derived lower-shriek is left adjoint to the exact derived module inverse image. -/
@[stacks 07AC "derived adjunction", stacks 07AD "derived Hom equivalence"]
noncomputable def adjunction
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}] :
    moduleLowerShriek.derived (J := J) (K := K) f R ⊣
      moduleInverseImage.derived (J := J) (K := K) f R :=
  (totalAdjunction (J := J) (K := K) f R).ofNatIsoRight
    (moduleInverseImage.totalDerivedIso (J := J) (K := K) f R)

/-- The derived lower-shriek/inverse-image Hom equivalence. -/
@[stacks 07AD "derived Hom equivalence"]
noncomputable def homEquiv
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}]
    (M : RingedSite.Hom.ModuleDerived.{z}
      (moduleInverseImage.source (J := J) (K := K) f R))
    (N : RingedSite.Hom.ModuleDerived.{z}
      (moduleInverseImage.target (K := K) R)) :
    ((moduleLowerShriek.derived (J := J) (K := K) f R).obj M ⟶ N) ≃
      (M ⟶ (moduleInverseImage.derived
        (J := J) (K := K) f R).obj N) :=
  (adjunction (J := J) (K := K) f R).homEquiv M N

/-- The derived lower-shriek/inverse-image Hom equivalence in the source-facing orientation. -/
@[stacks 07AD "derived Hom equivalence, inverse-image orientation"]
noncomputable def homEquivSymm
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w})
    [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}]
    (M : RingedSite.Hom.ModuleDerived.{z}
      (moduleInverseImage.source (J := J) (K := K) f R))
    (N : RingedSite.Hom.ModuleDerived.{z}
      (moduleInverseImage.target (K := K) R)) :
    (M ⟶ (moduleInverseImage.derived
      (J := J) (K := K) f R).obj N) ≃
      ((moduleLowerShriek.derived (J := J) (K := K) f R).obj M ⟶ N) :=
  (homEquiv (J := J) (K := K) f R M N).symm

/-- The homotopy-category model of the localized structure module at `U`. -/
@[stacks 07AC "homotopy generator"]
noncomputable abbrev structureModuleHomotopy
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) (U : C)
    [HasLowerShriek.{w}
      (inverseImageRingSheaf (J := J) (K := K) f R)]
    [UnivLE.{max uC vC, w}] :
    RingedSite.Hom.ModuleHomotopy.{w}
      (moduleInverseImage.source (J := J) (K := K) f R) :=
  (HomotopyCategory.singleFunctor
      (ModuleCat.{w} (moduleInverseImage.source (J := J) (K := K) f R)) 0).obj
    (structureModule (inverseImageRingSheaf (J := J) (K := K) f R) U)

/-- The localized structure module computes lower-shriek's total left-derived value. -/
@[stacks 07AC "generator computes derived lower shriek", instance]
theorem structureModuleComputesAt
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) (U : C)
    [HasLowerShriek.{w}
      (inverseImageRingSheaf (J := J) (K := K) f R)]
    [HasLowerShriek.{w} R]
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}] :
    Functor.LeftDerived.ComputesAt
      (moduleLowerShriek.toDerived (J := J) (K := K) f R)
      (RingedSite.Hom.ModuleQis.{w}
        (moduleInverseImage.source (J := J) (K := K) f R))
      (structureModuleHomotopy f R U) := sorry

/-- On a localized structure module, derived lower-shriek is computed by ordinary lower-shriek. -/
@[stacks 07AC "derived-to-underived generator isomorphism"]
noncomputable def structureModuleToUnderivedIso
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) (U : C)
    [HasLowerShriek.{w}
      (inverseImageRingSheaf (J := J) (K := K) f R)]
    [HasLowerShriek.{w} R]
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}] :
    (moduleLowerShriek.derived (J := J) (K := K) f R).obj
      ((DerivedCategory.singleFunctor
        (ModuleCat.{w} (moduleInverseImage.source (J := J) (K := K) f R)) 0).obj
        (structureModule (inverseImageRingSheaf (J := J) (K := K) f R) U)) ≅
      (DerivedCategory.singleFunctor
        (ModuleCat.{w} (moduleInverseImage.target (K := K) R)) 0).obj
        ((RingedSite.Cocontinuous.moduleLowerShriek (J := J) (K := K) f R).obj
          (structureModule (inverseImageRingSheaf (J := J) (K := K) f R) U)) :=
  (Functor.LeftDerived.ComputesAt.counitIso
      (moduleLowerShriek.toDerived (J := J) (K := K) f R)
      (RingedSite.Hom.ModuleQis.{w}
        (moduleInverseImage.source (J := J) (K := K) f R))
      (RingedSite.Hom.moduleLocalization
        (moduleInverseImage.source (J := J) (K := K) f R))
      (structureModuleHomotopy f R U) (structureModuleComputesAt f R U)) ≪≫
    (Functor.Homotopy.singleIso
      (RingedSite.Cocontinuous.moduleLowerShriek (J := J) (K := K) f R)
      0).app (structureModule (inverseImageRingSheaf (J := J) (K := K) f R) U)

/-- Lemma 21.37.2 (07AC): derived lower-shriek carries the localized structure module at `U`
to the localized structure module at `f.obj U`. -/
@[stacks 07AC "derived generator isomorphism"]
noncomputable def structureModuleIso
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) (U : C)
    [HasLowerShriek.{w}
      (inverseImageRingSheaf (J := J) (K := K) f R)]
    [HasLowerShriek.{w} R]
    [UnivLE.{max uC vC, w}] [UnivLE.{max uD vD, w}] :
    (moduleLowerShriek.derived (J := J) (K := K) f R).obj
      ((DerivedCategory.singleFunctor
        (ModuleCat.{w} (moduleInverseImage.source (J := J) (K := K) f R)) 0).obj
        (structureModule (inverseImageRingSheaf (J := J) (K := K) f R) U)) ≅
      (DerivedCategory.singleFunctor
        (ModuleCat.{w} (moduleInverseImage.target (K := K) R)) 0).obj
        (structureModule R (f.obj U)) :=
  structureModuleToUnderivedIso f R U ≪≫
    (DerivedCategory.singleFunctor
      (ModuleCat.{w} (moduleInverseImage.target (K := K) R)) 0).mapIso
      (moduleLowerShriek.structureModuleIso f R U)

end derived

end RingedSite.Cocontinuous.moduleLowerShriek
