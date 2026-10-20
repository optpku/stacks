module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Completion
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Tor
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Milnor sequences for derived completion

Over a Noetherian ring, derived completion is represented by the positive
ideal-power quotient tensor tower.  Its cohomology therefore fits into the
Milnor short exact sequence; for a module, the two outer towers are the
canonical positive ideal-power Tor systems.

@stack 0EET
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

-- Local instance justification (search instability): expose the standard
-- derived localization only while stating the completion Milnor sequences.
attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory.DerivedCompletion.Milnor

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

-- Local declaration justification (source-local notation): abbreviate the selected homology
-- functor in the two source-facing Milnor sequence statements.
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/-- The cohomology tower of the positive ideal-power derived tensor system for
a degree-zero module is the corresponding positive ideal-power Tor system. -/
@[stacks 0EET "derived tensor homology as the Tor system"]
theorem moduleTensorHomologySystem_eq_torSystem
    (I : Ideal A) (M : ModuleCat A) (p : ℕ) :
    CategoryTheory.DerivedCategory.IdealPower.tensorSystem I (ModuleCat.single0 M) ⋙
        H (-(p : ℤ)) =
      CategoryTheory.DerivedCategory.IdealPower.torSystem I M p := sorry
-- Proof strategy: ext stages and transition maps, then rewrite homology of the derived tensor
-- with a degree-zero module by the canonical Tor identification.

/-- Lemma 15.95.3 (1): the cohomology of the derived completion of a module
fits into the Milnor short exact sequence for its positive ideal-power Tor
systems. -/
@[stacks 0EET "(1), module Tor Milnor sequence"]
theorem moduleCohomologyShortExact (I : Ideal A) (M : ModuleCat A) (i : ℕ) :
    ∃ (ι :
        (CategoryTheory.DerivedCategory.IdealPower.torSystem I M (i + 1)).firstDerivedLimit ⟶
          (H (-(i : ℤ))).obj ((ModuleCat.single0 M)^∧[I, I.fg_of_isNoetherianRing]))
      (π :
        (H (-(i : ℤ))).obj ((ModuleCat.single0 M)^∧[I, I.fg_of_isNoetherianRing]) ⟶
          limit (CategoryTheory.DerivedCategory.IdealPower.torSystem I M i))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry
-- Proof strategy: apply `IsDerivedLimit.cohomologyShortExact` to the ideal-power tensor
-- tower and rewrite its two homology systems with `moduleTensorHomologySystem_eq_torSystem`.

/-- Lemma 15.95.3 (2): the derived completion of a bounded-above complex fits
into the Milnor short exact sequence for the cohomology of its positive
ideal-power quotient tensor tower. -/
@[stacks 0EET "(2), bounded-above Milnor sequence"]
theorem boundedAboveCohomologyShortExact
    (I : Ideal A) (K : DerivedCategory.Minus (ModuleCat A)) (i : ℕ) :
    ∃ (ι :
        SequentialInverseSystem.firstDerivedLimit
            (CategoryTheory.DerivedCategory.IdealPower.tensorSystem I K.obj ⋙
              H (-(i : ℤ) - 1)) ⟶
          (H (-(i : ℤ))).obj (K.obj^∧[I, I.fg_of_isNoetherianRing]))
      (π :
        (H (-(i : ℤ))).obj (K.obj^∧[I, I.fg_of_isNoetherianRing]) ⟶
          limit
            (CategoryTheory.DerivedCategory.IdealPower.tensorSystem I K.obj ⋙
              H (-(i : ℤ))))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry
-- Proof strategy: apply the general Milnor cohomology short exact sequence to the selected
-- derived limit of `tensorSystem I K.obj` and normalize the two adjacent cohomological degrees.

end DerivedCategory.DerivedCompletion.Milnor
