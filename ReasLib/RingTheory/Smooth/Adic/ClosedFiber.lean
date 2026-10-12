/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.FieldTheory.GeometricRegularity
public import ReasLib.RingTheory.LocalRing.ResidueField.ClosedFiber
public import ReasLib.RingTheory.RingHom.Fiber.Quotient
public import ReasLib.RingTheory.Smooth.Adic.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic Formal Smoothness and the Closed Fiber

@stack 07NQ
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u v

/-- Proposition 15.40.5 (07NQ): for a local homomorphism of Noetherian local rings, flatness
together with geometric regularity of the closed fiber, flatness together with adic formal
smoothness of the closed fiber, and maximal-ideal-adic formal smoothness of the original map are
equivalent. -/
@[stacks 07NQ "closed-fiber criterion for adic formal smoothness"]
theorem flat_geometricallyRegularSpecialFiber_formallySmooth_tfae
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalHom (algebraMap A B)] :
    List.TFAE [
      (algebraMap A B).Flat ∧
        Algebra.IsGeometricallyRegular (ResidueField A) (Ideal.Fiber (maximalIdeal A) B),
      (algebraMap A B).Flat ∧
        (algebraMap (ResidueField A) (Ideal.Fiber (maximalIdeal A) B)).formally_smooth_for_adic
          (maximalIdeal (Ideal.Fiber (maximalIdeal A) B)),
      (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)
    ] := sorry
