/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.KernelCokernel
public import ReasLib.CategoryTheory.Filtration.Strict.Abelian.Basic

/-!
# Coimages and Images of Filtered Morphisms

This file provides the abelian coimage-image part of the canonical factorization of a morphism
between filtered objects. The induced-filtered kernel and quotient-filtered cokernel themselves
live in `ReasLib.CategoryTheory.Filtration.KernelCokernel`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FilteredObject.Hom

open FilteredObject

variable [Abelian C]
variable {A B : FilteredObject C}

/-- The abelian coimage projection preserves the quotient filtration defining the filtered
coimage. -/
theorem toCoimage_preserves (f : A ⟶ B) (p : ℤ) :
    ((coimage f).filtration p).Factors
      ((A.filtration p).arrow ≫ Abelian.coimage.π f.hom) := sorry

/-- The canonical projection from a filtered object to the filtered coimage. -/
def toCoimage (f : A ⟶ B) : A ⟶ coimage f where
  hom := Abelian.coimage.π f.hom
  preserves := toCoimage_preserves f

/-- The underlying map of the filtered coimage projection is the abelian coimage projection. -/
@[simp]
theorem toCoimage_hom (f : A ⟶ B) :
    (toCoimage f).hom = Abelian.coimage.π f.hom := sorry

/-- The filtered kernel inclusion followed by the filtered coimage projection is zero. -/
theorem kernelι_comp_toCoimage (f : A ⟶ B) :
    kernelι f ≫ toCoimage f = 0 := sorry

/-- The canonical abelian image inclusion preserves the filtered image filtration. -/
theorem imageInclusion_preserves (f : A ⟶ B) (p : ℤ) :
    (B.filtration p).Factors (((image f).filtration p).arrow ≫ Abelian.image.ι f.hom) := sorry

/-- The canonical inclusion of the filtered image into the target. -/
def imageInclusion (f : A ⟶ B) : image f ⟶ B where
  hom := Abelian.image.ι f.hom
  preserves := imageInclusion_preserves f

/-- The filtered image inclusion followed by the filtered cokernel projection is zero. -/
theorem imageInclusion_comp_toCokernel (f : A ⟶ B) :
    imageInclusion f ≫ toCokernel f = 0 := sorry

namespace CoimageImageComparison

/-- The canonical filtered coimage-image factorization recovers the original morphism. -/
theorem factorization (f : A ⟶ B) :
    toCoimage f ≫ coimageImageComparison f ≫ imageInclusion f = f := sorry

end CoimageImageComparison

end FilteredObject.Hom

end CategoryTheory
