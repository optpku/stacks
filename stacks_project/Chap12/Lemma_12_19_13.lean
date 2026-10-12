/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.Finite
import StacksCheckRecall

/-!
# Lemma 12.19.13

Source-facing check for the six equivalent strictness criteria for a morphism of finite filtered
objects.  The finite-filtration detection theorem and all graded exactness bridges are owned by
`ReasLib.CategoryTheory.Filtration.Strict.Finite`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject.Hom

open FilteredObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B : FilteredObject C} (f : A ⟶ B)
variable (hA : IsFinite A) (hB : IsFinite B)

/- Lemma 12.19.13 [0127]: strictness, invertibility of the filtered and associated-graded
coimage-image comparisons, the two degreewise three-term exactness conditions, and the
degreewise five-term exactness condition are equivalent. -/
@[stacks 0127]
#check (CoimageImageComparison.Finite.strict_tfae f hA hB :
  List.TFAE
    [ Strict f
    , IsIso (coimageImageComparison f)
    , IsIso (associatedGradedMap (coimageImageComparison f))
    , ∀ p : ℤ, (Graded.Kernel.shortComplex f p).Exact
    , ∀ p : ℤ, (Graded.Cokernel.shortComplex f p).Exact
    , ∀ p : ℤ,
        (ComposableArrows.mk₅
          (0 : 0 ⟶ (kernel f).gradedPiece p)
          (gradedPieceMap (kernelι f) p)
          (gradedPieceMap f p)
          (gradedPieceMap (toCokernel f) p)
          (0 : (cokernel f).gradedPiece p ⟶ 0)).Exact
    ])

end CategoryTheory.FilteredObject.Hom
