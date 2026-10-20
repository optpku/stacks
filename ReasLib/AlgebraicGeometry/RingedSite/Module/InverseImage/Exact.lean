module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Exactness
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact module inverse image from a site presentation

A continuous and cocontinuous functor of sites presents module inverse image as an exact functor.
This leaf bundles that underived exactness for reuse by derived-category and cohomological APIs.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe z uC vC uD vD w

namespace RingedSite.Cocontinuous.moduleInverseImage

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The exact module inverse-image functor associated to a continuous and cocontinuous site
presentation. -/
@[stacks 04BD "exact module inverse image", stacks 07AC]
noncomputable abbrev exactFunctor
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) :
    RingedSite.ModuleCat.{z} (target (K := K) R) ⥤ₑ
      RingedSite.ModuleCat.{z} (source (J := J) (K := K) f R) :=
  ExactFunctor.of
    (RingedSite.Cocontinuous.moduleInverseImage (J := J) (K := K) f R)

end RingedSite.Cocontinuous.moduleInverseImage
