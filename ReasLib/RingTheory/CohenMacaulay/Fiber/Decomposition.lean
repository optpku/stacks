/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import ReasLib.RingTheory.CohenMacaulay.Fiber.Locus
public import ReasLib.RingTheory.CohenMacaulay.Ring
public import ReasLib.RingTheory.LocalRing.Product
public import ReasLib.Topology.KrullDimension.Equidimensional
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Decomposition by Cohen--Macaulay fiber dimension

@stack 00RL

This leaf packages the finite product decomposition of a flat finitely
presented algebra by the dimensions of its Cohen--Macaulay fibers.  The
component formula for `equiv` records that each projection is the canonical
quotient map; this keeps the product decomposition tied to its defining
ideals.
-/

universe u v

namespace Algebra.CohenMacaulayFiber

open PrimeSpectrum TopologicalSpace

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/-- A finite product decomposition whose factors are the nonempty
Cohen--Macaulay fiber-dimension strata. -/
@[stacks 00RL "decomposition by Cohen-Macaulay fiber dimension"]
structure Decomposition where
  /-- The fiber dimensions which occur. -/
  dimensions : Finset ℕ
  /-- A dimension is recorded exactly when its stratum is nonempty. -/
  mem_dimensions_iff (d : ℕ) :
    d ∈ dimensions ↔ (cohenMacaulayFiberDimensionStratum R S d).Nonempty
  /-- The ideal cutting out the factor of a given fiber dimension. -/
  ideal : dimensions → Ideal S
  /-- The product decomposition into the quotient factors. -/
  equiv : S ≃ₐ[R] ((d : dimensions) → S ⧸ ideal d)
  /-- Every component of `equiv` is the canonical quotient map. -/
  equiv_apply (s : S) (d : dimensions) :
    equiv s d = Ideal.Quotient.mk (ideal d) s
  /-- The `d`-th factor cuts out the fiber-dimension-`d` stratum. -/
  stratum_eq_zeroLocus (d : dimensions) :
    cohenMacaulayFiberDimensionStratum R S d =
      zeroLocus (ideal d : Set S)
  /-- Every quotient factor is finitely presented over the base. -/
  finitePresentation (d : dimensions) :
    Algebra.FinitePresentation R (S ⧸ ideal d)
  /-- Every quotient factor is flat over the base. -/
  flat (d : dimensions) : Module.Flat R (S ⧸ ideal d)
  /-- Every fiber of a quotient factor is Cohen--Macaulay. -/
  fiberCohenMacaulay (d : dimensions) (p : PrimeSpectrum R) :
    CohenMacaulayRing (p.asIdeal.Fiber (S ⧸ ideal d))
  /-- Every fiber of a quotient factor is equidimensional. -/
  fiberEquidimensional (d : dimensions) (p : PrimeSpectrum R) :
    EquidimensionalSpace (PrimeSpectrum (p.asIdeal.Fiber (S ⧸ ideal d)))
  /-- A nonempty fiber of the `d`-th factor has Krull dimension `d`. -/
  fiberDimension (d : dimensions) (p : PrimeSpectrum R)
      (_ : Nonempty (PrimeSpectrum (p.asIdeal.Fiber (S ⧸ ideal d)))) :
    ringKrullDim (p.asIdeal.Fiber (S ⧸ ideal d)) = (d : ℕ)

attribute [simp] Decomposition.equiv_apply
attribute [instance] Decomposition.finitePresentation Decomposition.flat
  Decomposition.fiberCohenMacaulay Decomposition.fiberEquidimensional
attribute [stacks 00RL "occurring fiber dimensions"] Decomposition.mem_dimensions_iff
attribute [stacks 00RL "canonical quotient components"] Decomposition.equiv_apply
attribute [stacks 00RL "fiber stratum cut out by a quotient ideal"]
  Decomposition.stratum_eq_zeroLocus
attribute [stacks 00RL "finite presentation of a dimension factor"]
  Decomposition.finitePresentation
attribute [stacks 00RL "flatness of a dimension factor"] Decomposition.flat
attribute [stacks 00RL "Cohen-Macaulay fibers of a dimension factor"]
  Decomposition.fiberCohenMacaulay
attribute [stacks 00RL "equidimensional fibers of a dimension factor"]
  Decomposition.fiberEquidimensional
attribute [stacks 00RL "dimension of a nonempty factor fiber"]
  Decomposition.fiberDimension

namespace Decomposition

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/-- Every dimension indexed by a decomposition has a nonempty stratum. -/
@[stacks 00RL "nonempty stratum of a recorded fiber dimension"]
theorem stratum_nonempty (D : Decomposition R S) (d : D.dimensions) :
    (cohenMacaulayFiberDimensionStratum R S d).Nonempty :=
  (D.mem_dimensions_iff d).mp d.property

/-- Forget the geometric specifications and retain the underlying finite
algebra-product decomposition. -/
@[stacks 00RL "underlying finite algebra-product decomposition"]
noncomputable def toAlgProduct (D : Decomposition R S) :
    AlgProduct.Decomposition.Finite R S := by
  let F : D.dimensions → Type v := fun d ↦ S ⧸ D.ideal d
  let eIndex : D.dimensions ≃ ULift.{v} D.dimensions := Equiv.ulift.symm
  let e : (∀ d, F d) ≃ₐ[R] (∀ d, F (eIndex.symm d)) :=
    AlgEquiv.piCongrLeft' R F eIndex
  exact AlgProduct.Decomposition.Finite.of (ι := ULift.{v} D.dimensions)
    (fun d ↦ F (eIndex.symm d)) (D.equiv.trans e)

/-- The generic product decomposition still evaluates by the canonical
quotient maps.  This hides the universe lift used for its index type. -/
@[simp, stacks 00RL "components of the underlying algebra product"]
theorem toAlgProduct_equiv_apply (D : Decomposition R S) (s : S)
    (d : ULift.{v} D.dimensions) :
    D.toAlgProduct.equiv s d = Ideal.Quotient.mk (D.ideal d.down) s := by
  change
    (AlgEquiv.piCongrLeft' R (fun d : D.dimensions ↦ S ⧸ D.ideal d)
      Equiv.ulift.symm (D.equiv s)) d = _
  rw [AlgEquiv.piCongrLeft'_apply, Equiv.piCongrLeft'_apply]
  exact D.equiv_apply s d.down

/-- The three pointwise fiber properties of a decomposition, with
Cohen--Macaulayness and equidimensionality asserted independently of
nonemptiness. -/
@[stacks 00RL "fiber properties of a dimension factor"]
theorem fiber_spec (D : Decomposition R S) (d : D.dimensions)
    (p : PrimeSpectrum R) :
    CohenMacaulayRing (p.asIdeal.Fiber (S ⧸ D.ideal d)) ∧
      EquidimensionalSpace (PrimeSpectrum (p.asIdeal.Fiber (S ⧸ D.ideal d))) ∧
        (Nonempty (PrimeSpectrum (p.asIdeal.Fiber (S ⧸ D.ideal d))) →
          ringKrullDim (p.asIdeal.Fiber (S ⧸ D.ideal d)) = (d : ℕ)) :=
  ⟨D.fiberCohenMacaulay d p, D.fiberEquidimensional d p, D.fiberDimension d p⟩

/-- The complete specification of a fiber-dimension decomposition.  This is
the unbundled view used by source statements and consumers which do not need
to retain the record. -/
@[stacks 00RL "specification of a fiber-dimension decomposition"]
theorem spec (D : Decomposition R S) :
    (∀ d : ℕ,
      d ∈ D.dimensions ↔
        (cohenMacaulayFiberDimensionStratum R S d).Nonempty) ∧
      (∀ (s : S) (d : D.dimensions),
      D.equiv s d = Ideal.Quotient.mk (D.ideal d) s) ∧
      (∀ d : D.dimensions,
        cohenMacaulayFiberDimensionStratum R S d =
          zeroLocus (D.ideal d : Set S)) ∧
        ∀ d : D.dimensions,
          (cohenMacaulayFiberDimensionStratum R S d).Nonempty ∧
            Algebra.FinitePresentation R (S ⧸ D.ideal d) ∧
              Module.Flat R (S ⧸ D.ideal d) ∧
                ∀ p : PrimeSpectrum R,
                  CohenMacaulayRing (p.asIdeal.Fiber (S ⧸ D.ideal d)) ∧
                    EquidimensionalSpace
                      (PrimeSpectrum (p.asIdeal.Fiber (S ⧸ D.ideal d))) ∧
                      (Nonempty (PrimeSpectrum (p.asIdeal.Fiber (S ⧸ D.ideal d))) →
                        ringKrullDim (p.asIdeal.Fiber (S ⧸ D.ideal d)) = (d : ℕ)) := by
  refine ⟨D.mem_dimensions_iff, D.equiv_apply, D.stratum_eq_zeroLocus, ?_⟩
  intro d
  exact ⟨D.stratum_nonempty d, D.finitePresentation d, D.flat d,
    fun p ↦ D.fiber_spec d p⟩

end

/-- A flat finitely presented algebra with Cohen--Macaulay fibers admits a
decomposition by its occurring fiber dimensions. -/
@[stacks 00RL "existence of the fiber-dimension decomposition"]
theorem nonempty_of_finitePresentation_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (hCM : ∀ p : PrimeSpectrum R, CohenMacaulayRing (p.asIdeal.Fiber S)) :
    Nonempty (Decomposition R S) := sorry

end Decomposition

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]
variable (D : Algebra.CohenMacaulayFiber.Decomposition R S)
variable (d : D.dimensions) (p : PrimeSpectrum R)

#synth Algebra.FinitePresentation R (S ⧸ D.ideal d)
#synth Module.Flat R (S ⧸ D.ideal d)
#synth CohenMacaulayRing (p.asIdeal.Fiber (S ⧸ D.ideal d))
#synth EquidimensionalSpace (PrimeSpectrum (p.asIdeal.Fiber (S ⧸ D.ideal d)))

end

end Algebra.CohenMacaulayFiber
