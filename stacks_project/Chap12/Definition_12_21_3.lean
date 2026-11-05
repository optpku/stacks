/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.ExactCouple.Derived
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (X : ExactCouple C)

/-!
# Compatibility entry for Definition 12.21.3

The reusable construction of derived exact couples and their associated spectral sequence lives in
`ReasLib.CategoryTheory.Homology.ExactCouple.Derived`.
-/

/- Definition 12.21.3 (011S): deriving an exact couple replaces its outer object by the image of
its endomorphism and its page object by the homology of the page differential. Iterating this
construction gives the successive pages of the associated spectral sequence. -/
#check (ExactCouple.Derived.construction C : ExactCouple.Derived.Construction C)

@[stacks 011S "(1)"]
#check (ExactCouple.Derived.derived X : ExactCouple C)

#check (ExactCouple.Derived.iterate X : ℕ → ExactCouple C)
#check (ExactCouple.Derived.Construction.Iteration.zero
  (ExactCouple.Derived.construction C) X)
#check (ExactCouple.Derived.Construction.Iteration.zero_E
  (ExactCouple.Derived.construction C) X)
#check (ExactCouple.Derived.Construction.Iteration.zero_d
  (ExactCouple.Derived.construction C) X)
#check (ExactCouple.Derived.Construction.Iteration.succ
  (ExactCouple.Derived.construction C) X)

@[stacks 011S "(2)"]
#check (ExactCouple.Derived.associatedSpectralSequence X :
  SpectralSequence C (fun _ : ℤ ↦ ComplexShape.refl PUnit.{1}) 1)

#check ExactCouple.Derived.Page.complex
#check ExactCouple.Derived.Page.obj
#check ExactCouple.Derived.Page.differential

end
end CategoryTheory
