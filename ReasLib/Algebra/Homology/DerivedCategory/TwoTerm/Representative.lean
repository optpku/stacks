/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-term representatives of derived modules

This file owns the predicate that a cochain complex represents a derived module in degrees
`-1` and `0`, its basic existence criteria, and its behavior under scalar extension.

@stack 0G9E
@stack 0G9G
-/

@[expose] public section

open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace CategoryTheory

/-- A cochain complex `P` is a two-term representative of `K` when `Q(P) ≅ K` and `P` is
supported in degrees `-1` and `0`. -/
@[stacks 0G9E "two-term representative"]
def IsTwoTermRepresentative
    {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat R))
    (P : CochainComplex (ModuleCat R) ℤ) : Prop :=
  IsIsomorphic (DerivedCategory.Q.obj P) K ∧ P.IsStrictlyGE (-1) ∧ P.IsStrictlyLE 0

namespace IsTwoTermRepresentative

/-- A derived `R`-module concentrated in degrees `-1` and `0` admits a
two-term representative whose degree-zero term is free. -/
@[stacks 0G9E "free two-term representative"]
theorem exists_free
    {R : Type u} [Ring R]
    (K : DerivedCategory (ModuleCat R))
    (hGE : K.IsGE (-1)) (hLE : K.IsLE 0) :
    ∃ P : CochainComplex (ModuleCat R) ℤ,
      IsTwoTermRepresentative K P ∧ Module.Free R (P.X 0) := sorry
/- Proof strategy: choose a bounded-above free resolution of `K`, cut it at degree `-1`, and use
the supplied cohomological bounds to identify the quotient complex with `K`.  The degree-zero
term is unchanged by the cut and remains free. -/

/-- Over a Noetherian ring, finite cohomology in degrees `-1` and `0` gives
a two-term representative with finite free degree-zero term and finite degree-`-1` term. -/
@[stacks 0G9E "finite two-term representative"]
theorem exists_finiteFree
    {R : Type u} [Ring R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat R))
    (hGE : K.IsGE (-1)) (hLE : K.IsLE 0)
    (hHneg1 : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj K))
    (hH0 : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj K)) :
    ∃ P : CochainComplex (ModuleCat R) ℤ,
      IsTwoTermRepresentative K P ∧
        Module.Free R (P.X 0) ∧ Module.Finite R (P.X 0) ∧ Module.Finite R (P.X (-1)) := sorry
/- Proof strategy: use Noetherianity and finite cohomology to choose a bounded-above finite-free
pseudo-coherent model, truncate it to degrees `-1` and `0`, and transport the resulting
quasi-isomorphism through `DerivedCategory.Q`; finiteness of the boundary term follows from the
Noetherian kernel/cokernel API. -/

/-- Scalar extension of a two-term
representative whose degree-zero term is flat represents the truncation in degrees `≥ -1` of the
derived scalar extension. -/
@[stacks 0G9G]
theorem extension_truncGE
    {R S : Type u} [CommRing R] [CommRing S]
    (σ : R →+* S)
    {K : DerivedCategory (ModuleCat R)} {P : CochainComplex (ModuleCat R) ℤ}
    (hP : IsTwoTermRepresentative K P)
    (hflat0 : Module.Flat R (P.X 0)) :
    IsTwoTermRepresentative
      ((t.truncGE (-1)).obj ((ModuleCat.derivedExtensionOfScalars σ).obj K))
      (((ModuleCat.extendScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := sorry
/- Proof strategy: extend the representative termwise along `σ`.  Flatness of `P.X 0` controls
the boundary homology in degree `-1`, so the scalar-extended two-term complex computes
`t.truncGE (-1)` of derived extension; use the scalar-extension comparison isomorphism and
transport strict support degreewise. -/

end IsTwoTermRepresentative

end CategoryTheory
