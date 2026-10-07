module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived sections of module inverse image

This file owns the objectwise derived-sections comparison for the continuous presentation of
module inverse image.  It deliberately uses `RingedSite.Cocontinuous.moduleInverseImage` instead
of manufacturing a bundled morphism of ringed sites.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe z uC vC uD vD w

namespace RingedSite.Cocontinuous.moduleInverseImage

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Stacks 0DD8 (2): derived additive sections of module inverse image over `U` agree with
derived additive sections over `f.obj U`. -/
@[stacks 0DD8 "module inverse image and sections"]
theorem sectionsIso
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) (U : C)
    [UnivLE.{max uC vC, z}] [UnivLE.{max uD vD, z}]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.ModuleSections.Underlying.sectionsToDerived.{z}
        (source (J := J) (K := K) f R) U)
      (RingedSite.Hom.ModuleQis.{z} (source (J := J) (K := K) f R))]
    [Functor.HasRightDerivedFunctor
      (RingedSite.Hom.ModuleSections.Underlying.sectionsToDerived.{z}
        (target (K := K) R) (f.obj U))
      (RingedSite.Hom.ModuleQis.{z} (target (K := K) R))]
    (M : RingedSite.Hom.ModuleDerived.{z} (target (K := K) R)) :
    IsIsomorphic
      ((RingedSite.Hom.ModuleSections.Underlying.sectionsDerived.{z}
          (source (J := J) (K := K) f R) U).obj
        ((derived (J := J) (K := K) f R).obj M))
      ((RingedSite.Hom.ModuleSections.Underlying.sectionsDerived.{z}
          (target (K := K) R) (f.obj U)).obj M) := sorry

end RingedSite.Cocontinuous.moduleInverseImage
