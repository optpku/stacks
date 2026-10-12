/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of Sequential Homotopy Limits

This derived-category application states the Milnor short exact sequence for cohomology of a
sequential homotopy limit.  The homotopy-limit hypothesis uses the presentation-independent
predicate `HomotopyLimit.IsOf`; exactness of the countable product is an explicit mathematical
input.

The theorem is not part of the generic pretriangulated homotopy-limit umbrella: its observer is
the derived-category cohomology functor.
@stack 07KY
@stack 0EGS
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory.HomotopyLimit.IsOf

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [HasCountableProducts C] [HasExactLimitsOfShape (Discrete ℕ) C]
  [HasLimitsOfShape ℕᵒᵖ C]

/-- The cohomology of a sequential homotopy limit fits into the Milnor short exact sequence,
whose left term is the canonical first derived inverse limit of the preceding cohomology tower. -/
@[stacks 07KY]
theorem cohomologyShortExact
    {Ksys : SequentialInverseSystem (DerivedCategory C)} {Klim : DerivedCategory C}
    (hKlim : HomotopyLimit.IsOf Ksys Klim) (p : ℤ) :
    ∃ (ι : SequentialInverseSystem.Milnor.ProductCone.canonicalR1
        (Ksys ⋙ DerivedCategory.homologyFunctor C (p - 1)) ⟶
        (DerivedCategory.homologyFunctor C p).obj Klim)
      (π : (DerivedCategory.homologyFunctor C p).obj Klim ⟶
        limit (Ksys ⋙ DerivedCategory.homologyFunctor C p))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

/-- If the preceding cohomology tower is Mittag-Leffler, the Milnor short exact sequence
identifies the cohomology of a sequential homotopy limit with the inverse limit of the cohomology
tower. -/
@[stacks 0EGS "Mittag-Leffler degeneration of the cohomology Milnor sequence"]
theorem cohomologyIsIsomorphicLimit
    {Ksys : SequentialInverseSystem (DerivedCategory C)} {Klim : DerivedCategory C}
    (hKlim : HomotopyLimit.IsOf Ksys Klim) (p : ℤ)
    (hML : SequentialInverseSystem.IsMittagLeffler
      (Ksys ⋙ DerivedCategory.homologyFunctor C (p - 1))) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor C p).obj Klim)
      (limit (Ksys ⋙ DerivedCategory.homologyFunctor C p)) := sorry

end CategoryTheory.HomotopyLimit.IsOf

end
