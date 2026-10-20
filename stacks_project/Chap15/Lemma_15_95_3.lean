/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Milnor
import StacksCheckRecall

/-!
# Milnor sequences for derived completion

@stack 0EET
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

-- Local instance justification (search instability): expose the standard
-- derived localization only while spelling the source Milnor sequences.
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/- Lemma 15.95.3 (1): the cohomology of the derived completion of a module sits between
`R¹ lim Tor_{i+1}` and `lim Tor_i` in a short exact sequence. -/
@[stacks 0EET "(1), module Tor Milnor sequence"]
#check fun (I : Ideal A) (M : ModuleCat A) (i : ℕ) ↦
  (DerivedCategory.DerivedCompletion.Milnor.moduleCohomologyShortExact I M i :
    ∃ (ι :
        (CategoryTheory.DerivedCategory.IdealPower.torSystem I M (i + 1)).firstDerivedLimit ⟶
          (H (-(i : ℤ))).obj
            ((ModuleCat.single0 M)^∧[I, I.fg_of_isNoetherianRing]))
      (π :
        (H (-(i : ℤ))).obj
            ((ModuleCat.single0 M)^∧[I, I.fg_of_isNoetherianRing]) ⟶
          limit (CategoryTheory.DerivedCategory.IdealPower.torSystem I M i))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact)

/- Lemma 15.95.3 (2): the analogous Milnor short exact sequence holds for a bounded-above
derived object. -/
@[stacks 0EET "(2), bounded-above Milnor sequence"]
#check fun (I : Ideal A) (K : DerivedCategory.Minus (ModuleCat A)) (i : ℕ) ↦
  (DerivedCategory.DerivedCompletion.Milnor.boundedAboveCohomologyShortExact I K i :
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
      (ShortComplex.mk ι π h).ShortExact)

#check fun (I : Ideal A) (M : ModuleCat A) (p : ℕ) ↦
  (CategoryTheory.DerivedCategory.IdealPower.torSystem I M p :
    SequentialInverseSystem (ModuleCat A))

#check fun (I : Ideal A) (M : ModuleCat A) (p : ℕ) ↦
  (DerivedCategory.DerivedCompletion.Milnor.moduleTensorHomologySystem_eq_torSystem I M p :
    CategoryTheory.DerivedCategory.IdealPower.tensorSystem I (ModuleCat.single0 M) ⋙
        H (-(p : ℤ)) =
      CategoryTheory.DerivedCategory.IdealPower.torSystem I M p)
