module

public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.Strict.Abelian

/-!
# Strict Morphisms of Finite Filtered Objects

For finite filtrations, a filtered morphism is strict exactly when its coimage-image comparison
is detected as an isomorphism on associated graded objects.  This leaf records the pointwise
kernel and cokernel criteria and the source-facing six-condition equivalence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject.Hom

open FilteredObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B : FilteredObject C}

namespace CoimageImageComparison

namespace Finite

/-- For finite filtrations, an isomorphism on associated graded objects detects an isomorphism of
the filtered coimage-image comparison. -/
theorem isIso_of_associatedGraded_isIso
    (f : A ⟶ B) (hA : IsFinite A) (hB : IsFinite B)
    [IsIso (associatedGradedMap (coimageImageComparison f))] :
    IsIso (coimageImageComparison f) := sorry

namespace Kernel

/-- For finite filtrations, kernel-side exactness in every degree detects the filtered
coimage-image isomorphism. -/
theorem isIso_of_exact
    (f : A ⟶ B) (hA : IsFinite A) (hB : IsFinite B)
    (hExact : ∀ p : ℤ, (FilteredObject.Hom.Graded.Kernel.shortComplex f p).Exact) :
    IsIso (coimageImageComparison f) := sorry

/-- For finite filtrations, kernel-side exactness in every degree detects the associated-graded
coimage-image isomorphism. -/
theorem associated_isIso_of_exact
    (f : A ⟶ B) (hA : IsFinite A) (hB : IsFinite B)
    (hExact : ∀ p : ℤ, (FilteredObject.Hom.Graded.Kernel.shortComplex f p).Exact) :
    IsIso (associatedGradedMap (coimageImageComparison f)) := sorry

end Kernel

namespace Cokernel

/-- For finite filtrations, cokernel-side exactness in every degree detects the filtered
coimage-image isomorphism. -/
theorem isIso_of_exact
    (f : A ⟶ B) (hA : IsFinite A) (hB : IsFinite B)
    (hExact : ∀ p : ℤ, (FilteredObject.Hom.Graded.Cokernel.shortComplex f p).Exact) :
    IsIso (coimageImageComparison f) := sorry

/-- For finite filtrations, cokernel-side exactness in every degree detects the associated-graded
coimage-image isomorphism. -/
theorem associated_isIso_of_exact
    (f : A ⟶ B) (hA : IsFinite A) (hB : IsFinite B)
    (hExact : ∀ p : ℤ, (FilteredObject.Hom.Graded.Cokernel.shortComplex f p).Exact) :
    IsIso (associatedGradedMap (coimageImageComparison f)) := sorry

end Cokernel

/-- For a morphism of finite filtered objects in an abelian category, strictness, filtered and
graded coimage-image isomorphisms, the two three-term graded exactness conditions, and the
corresponding five-term graded exactness condition are equivalent. -/
@[stacks 0127]
theorem strict_tfae
    (f : A ⟶ B) (hA : IsFinite A) (hB : IsFinite B) :
    List.TFAE
      [ Strict f
      , IsIso (coimageImageComparison f)
      , IsIso (associatedGradedMap (coimageImageComparison f))
      , ∀ p : ℤ, (FilteredObject.Hom.Graded.Kernel.shortComplex f p).Exact
      , ∀ p : ℤ, (FilteredObject.Hom.Graded.Cokernel.shortComplex f p).Exact
      , ∀ p : ℤ,
          (ComposableArrows.mk₅
            (0 : 0 ⟶ (kernel f).gradedPiece p)
            (gradedPieceMap (kernelι f) p)
            (gradedPieceMap f p)
            (gradedPieceMap (toCokernel f) p)
            (0 : (cokernel f).gradedPiece p ⟶ 0)).Exact
      ] := sorry

end Finite

end CoimageImageComparison

end CategoryTheory.FilteredObject.Hom
