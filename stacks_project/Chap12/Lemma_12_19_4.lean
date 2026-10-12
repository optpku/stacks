/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.Abelian
import StacksCheckRecall

/-!
# Lemma 12.19.4

Source-facing checks for the canonical coimage-image criterion for strict morphisms of filtered
objects.  The filtered subobject, quotient, coimage, image, and comparison constructions are
owned by `ReasLib.CategoryTheory.Filtration.Strict.Abelian`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B : FilteredObject C} (f : A ⟶ B)

/- The reusable owner exposes the filtered coimage, image, and their canonical comparison as
concrete data. -/
#check (coimage f : FilteredObject C)
#check (image f : FilteredObject C)
#check (CoimageImageComparison.Subobject.map f :
  coimage f ⟶ B.subobject (imageSubobject f.hom))
#check (Image.subobjectIso f :
  B.subobject (imageSubobject f.hom) ≅ image f)
#check (coimageImageComparison f : coimage f ⟶ image f)

/- Lemma 12.19.4 [05SI]: strictness is equivalent to invertibility of the canonical filtered
coimage-image comparison. -/
@[stacks 05SI]
#check (strict_iff_coimageImageComparison_isIso f :
  Strict f ↔ IsIso (coimageImageComparison f))

end CategoryTheory.FilteredObject.Hom
