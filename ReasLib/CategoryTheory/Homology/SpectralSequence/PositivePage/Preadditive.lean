/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PositivePage.OfZero
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of positive-page evaluation

The positive-page and page-entry evaluations are ordinary additive functors once the spectral
sequence category carries its shared preadditive structure.  This leaf keeps those instances out
of the page-definition file, so clients that only need additive transport can import this module.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory
namespace SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type*} {c : ℤ → ComplexShape κ}

namespace Page.One

/-- Forgetting the zeroth page is additive on spectral-sequence morphisms. -/
@[stacks 0BDU "additivity of the page-one view functor"]
noncomputable instance functor_additive :
    (functor (C := C) c).Additive := sorry

end Page.One

namespace PositivePageFunctor

/-- Evaluation at a fixed positive page is additive in spectral-sequence morphisms. -/
@[stacks 011O "additivity of positive-page evaluation"]
noncomputable instance additive (r : ℕ+) :
    (positivePageFunctor (C := C) c r).Additive := sorry

end PositivePageFunctor

namespace PageObjectFunctor

/-- Evaluation at a fixed positive-page entry is additive in spectral-sequence morphisms. -/
@[stacks 011O "additivity of positive-page entry evaluation"]
noncomputable instance additive (r : ℕ+) (pq : κ) :
    (pageObjectFunctor (C := C) c r pq).Additive := sorry

end PageObjectFunctor

end SpectralSequence
end CategoryTheory
