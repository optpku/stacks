/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Hilbert.DiscreteValuationRing
import StacksCheckRecall

/-!
# Lemma 62.6.10

Surjectivity of the Hilbert cycle-class homomorphism over a discrete valuation
ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RelativeCycle

/- Lemma 62.6.10: if `f : X ⟶ S` is of finite type and `S` is the spectrum of a
discrete valuation ring, then for every `r ≥ 0` the Hilbert cycle-class
homomorphism `cycleClassHomToGroup` (62.6.8.1) from `FreeAbelianGroup (Hilb f r)`
to `group f r` is surjective. -/
@[stacks 0H5A] #check (AlgebraicGeometry.RelativeCycle.cycleClassHomToGroup_surjective :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [f.FiniteType] (r : ℕ),
      Function.Surjective (cycleClassHomToGroup f r))

/- Every relative `r`-cycle on `X / Spec R` lies in the image of
`cycleClassHom`. -/
#check (AlgebraicGeometry.RelativeCycle.mem_range_cycleClassHom :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [f.FiniteType] (r : ℕ)
      {α : f.FiberCycleFamily r}, IsRelative α → α ∈ Set.range (cycleClassHom f r))

end AlgebraicGeometry.RelativeCycle
