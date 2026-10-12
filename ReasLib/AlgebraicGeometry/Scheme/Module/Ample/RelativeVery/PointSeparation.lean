/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NonvanishingLocus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery

/-!
# Point separation by relatively very ample modules

Sections of a relatively very ample module over an infinite field can separate a rational point
from a prescribed finite family of other points.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RelativelyVeryAmple

/-- A relatively very ample module on a finite-type scheme over an infinite field has a global
section vanishing at a rational point and nonvanishing at every point of a prescribed finite
family disjoint from it. -/
theorem exists_section_vanishingAt_nonvanishingAt
    {k : Type u} [Field k] [Infinite k]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)} [Scheme.Hom.FiniteType f]
    {L : X.Modules} (hL : AlgebraicGeometry.RelativelyVeryAmple f L)
    (x : X) [IsIso (f.residueFieldMap x)]
    {n : ℕ} (xs : Fin n → X) (hxs : ∀ i : Fin n, x ≠ xs i) :
    ∃ s : L.sections,
      x ∉ RingedSpace.sectionNonvanishingLocus X.toRingedSpace L s ∧
        ∀ i : Fin n, xs i ∈ RingedSpace.sectionNonvanishingLocus X.toRingedSpace L s := sorry

end AlgebraicGeometry.RelativelyVeryAmple
