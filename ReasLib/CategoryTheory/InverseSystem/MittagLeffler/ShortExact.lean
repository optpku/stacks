module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.EventualZero
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Shift
public import ReasLib.CategoryTheory.InverseSystem.ShortExact
public import ReasLib.CategoryTheory.InverseSystem.TailDecomposition
public import ReasLib.CategoryTheory.Subobject.Image

/-!
# Mittag-Leffler Conditions in Short Exact Inverse-System Rows

This leaf gives the stable-image comparison theorems for the first two terms of a short exact
sequence of sequential inverse systems.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.ShortComplex.ShortExact

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace MittagLeffler

/-- The quotient term of a short exact row of sequential inverse
systems is Mittag-Leffler whenever the middle term is Mittag-Leffler. -/
@[stacks 02N1]
theorem right_of_middle {S : ShortComplex (SequentialInverseSystem A)}
    (hS : S.ShortExact) (hX₂ : S.X₂.IsMittagLeffler) :
    S.X₃.IsMittagLeffler := sorry

/-- In a short exact row of sequential inverse systems, the middle
inverse system is Mittag-Leffler when both outer inverse systems are Mittag-Leffler. -/
@[stacks 0CQB]
theorem middle_of_left_right {S : ShortComplex (SequentialInverseSystem A)}
    (hS : S.ShortExact) (hX₁ : S.X₁.IsMittagLeffler) (hX₃ : S.X₃.IsMittagLeffler) :
    S.X₂.IsMittagLeffler := sorry

/-- In a short exact row, if the left inverse system is Mittag-Leffler, then the middle and
right inverse systems are Mittag-Leffler simultaneously. -/
theorem middle_iff_right_of_left {S : ShortComplex (SequentialInverseSystem A)}
    (hS : S.ShortExact) (hX₁ : S.X₁.IsMittagLeffler) :
    S.X₂.IsMittagLeffler ↔ S.X₃.IsMittagLeffler := sorry

namespace Right

/-- If the right inverse system has eventually zero transition maps, the first two terms of a
short exact inverse-system row are Mittag-Leffler simultaneously. -/
theorem left_iff_middle_of_eventuallyZero
    {T : ShortComplex (SequentialInverseSystem A)} (hT : T.ShortExact)
    (hzero : PreorderInverseSystem.Transition.EventuallyZero T.X₃) :
    T.X₁.IsMittagLeffler ↔ T.X₂.IsMittagLeffler := sorry

/-- If the right inverse system is literally constant, the first two terms of a short exact
inverse-system row are Mittag-Leffler simultaneously. -/
theorem left_iff_middle_of_constant
    {C : A} {T : ShortComplex (SequentialInverseSystem A)} (hT : T.ShortExact)
    (hX₃ : T.X₃ = (Functor.const ℕᵒᵖ).obj C) :
    T.X₁.IsMittagLeffler ↔ T.X₂.IsMittagLeffler := sorry

/-- If the quotient inverse system in a short exact row is essentially
constant, then the first inverse system is Mittag-Leffler exactly when the middle inverse system
is Mittag-Leffler. -/
@[stacks 070D]
theorem left_iff_middle_of_essentiallyConstant
    {S : ShortComplex (SequentialInverseSystem A)} (hS : S.ShortExact)
    (hC : IsCofiltered.IsEssentiallyConstant S.X₃) :
    S.X₁.IsMittagLeffler ↔ S.X₂.IsMittagLeffler := sorry

end Right

end MittagLeffler

end CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory.SequentialInverseSystem

variable {A : Type u} [Category.{v} A]

namespace IsMittagLeffler

/-- The Mittag-Leffler property of sequential inverse systems in an abelian category is closed
under epimorphic quotients. -/
@[stacks 02N1 "Mittag-Leffler inverse systems are closed under quotients"]
instance isClosedUnderQuotients [Abelian A] :
    ObjectProperty.IsClosedUnderQuotients
      (fun F : SequentialInverseSystem A ↦ F.IsMittagLeffler) := sorry

end IsMittagLeffler

end CategoryTheory.SequentialInverseSystem
