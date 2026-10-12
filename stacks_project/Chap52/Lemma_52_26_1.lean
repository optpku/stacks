/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.«52_25_1_1_EulerCharacteristic»
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.RingTheory.Depth
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open scoped ENat

universe u

namespace AlgebraicGeometry.CoherentTripleSetup

/-- Lemma 52.26.1: for a Noetherian local ring `A`, a regular element `f` in its
maximal ideal, and depth `A` at least three, restriction from the punctured
spectrum of `A` to that of `A / fA` is injective on torsion Picard classes. -/
@[stacks 0F2A]
theorem picardPullback_injective_on_torsion
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f)
    (hdepth : (3 : ℕ∞) ≤ moduleDepth A A) :
    let S := CoherentTripleSetup.ofElement f hf_mem hf_regular
    let U := S.algebraization.U
    Set.InjOn (Scheme.Hom.picardPullback S.closedFiberOnU)
      (AddCommGroup.torsion (Scheme.PicardGroup U.toScheme)) := sorry

end AlgebraicGeometry.CoherentTripleSetup
