module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.Filtration.Functors
public import ReasLib.CategoryTheory.Filtration.Induced
public import ReasLib.CategoryTheory.Filtration.Strict
public import ReasLib.CategoryTheory.Filtration.ZeroMorphisms
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic Abelian Constructions for Filtered Objects

This file owns the canonical filtered coimage-image comparison and its graded exact rows.
The generic induced-subobject and quotient-filtered-object constructions live in
`ReasLib.CategoryTheory.Filtration.Induced`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FilteredObject

section SubobjectGraded

variable (A : FilteredObject C) [Abelian C] (X : Subobject A.obj)

namespace Subobject.Graded

/-- The canonical graded-piece row associated to a filtered subobject and its quotient. -/
def shortComplex (p : ℤ) : ShortComplex C :=
  ShortComplex.mk
    (Hom.gradedPieceMap (A.subobjectι X) p)
    (Hom.gradedPieceMap (Subobject.quotientπ A X) p)
    (Hom.gradedPieceMap_comp_zero (A.subobjectι X) (Subobject.quotientπ A X)
      (Subobject.subobjectι_comp_quotientπ A X) p)

/-- The associated-graded sequence of an induced subobject filtration and its quotient is short
exact in every degree. -/
@[stacks 05SP]
theorem shortExact (p : ℤ) :
    (shortComplex A X p).ShortExact := sorry

end Subobject.Graded

end SubobjectGraded

end FilteredObject

namespace FilteredObject.Hom

open FilteredObject

variable [Abelian C]
variable {A B : FilteredObject C}

/-! ## Filtered coimages and images -/

/-- The filtered coimage, with quotient filtration induced from the source. -/
abbrev coimage (f : A ⟶ B) : FilteredObject C :=
  { obj := Abelian.coimage f.hom
    filtration := A.filtration.quotient (Abelian.coimage.π f.hom) }

/-- The filtered image, obtained by transporting the induced filtration on the image subobject to
the canonical abelian image object. -/
abbrev image (f : A ⟶ B) : FilteredObject C :=
  (B.subobject (imageSubobject f.hom)).ofIso
    (imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm)

namespace CoimageImageComparison
namespace Subobject

/-- The canonical filtered morphism from the coimage to the literal image-subobject model. -/
def map (f : A ⟶ B) :
    coimage f ⟶ B.subobject (imageSubobject f.hom) where
  hom :=
    Abelian.coimageImageComparison f.hom ≫
      (imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm).inv
  preserves := sorry

end Subobject
end CoimageImageComparison

namespace Image

/-- The literal filtered image-subobject model is canonically isomorphic to the filtered abelian
image. -/
def subobjectIso (f : A ⟶ B) :
    B.subobject (imageSubobject f.hom) ≅ image f where
  hom :=
    { hom := (imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm).hom
      preserves := sorry }
  inv :=
    { hom := (imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm).inv
      preserves := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

end Image

/-- The canonical comparison from the filtered coimage to the filtered image. -/
def coimageImageComparison (f : A ⟶ B) : coimage f ⟶ image f :=
  CoimageImageComparison.Subobject.map f ≫ (Image.subobjectIso f).hom

/-- The underlying morphism of the filtered comparison is the abelian coimage-image comparison. -/
@[simp]
theorem coimageImageComparison_hom (f : A ⟶ B) :
    (coimageImageComparison f).hom = Abelian.coimageImageComparison f.hom := sorry

/-- A filtered morphism is strict exactly when its filtered coimage-image comparison is an
isomorphism. -/
@[stacks 05SI]
theorem strict_iff_coimageImageComparison_isIso (f : A ⟶ B) :
    Strict f ↔ IsIso (coimageImageComparison f) := sorry

end FilteredObject.Hom

end CategoryTheory
