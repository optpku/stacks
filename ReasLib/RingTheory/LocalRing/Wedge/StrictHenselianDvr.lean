/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.RingTheory.Henselian.StrictHenselian
public import ReasLib.RingTheory.LocalRing.Wedge.Basic

/-!
# Strictly henselian DVR wedge factors

This leaf packages the finite families of strictly henselian discrete valuation
rings that occur as wedge factors of a one-dimensional local ring.
-/

@[expose] public section

universe u v

namespace LocalRing.Wedge

/-- A finite family of strictly henselian discrete valuation rings indexed by
`Fin (m + 1)`. -/
structure StrictHenselianDvrFamily (m : ℕ) where
  /-- The component ring at each index. -/
  carrier : Fin (m + 1) → Type v
  /-- Each component is a commutative ring. -/
  instCommRing : ∀ i, CommRing (carrier i)
  /-- Each component is a strictly henselian local ring. -/
  instStrictHenselian : ∀ i, StrictHenselianLocalRing (carrier i)
  /-- Each component is a domain. -/
  instDomain : ∀ i, IsDomain (carrier i)
  /-- Each component is a discrete valuation ring. -/
  instDvr : ∀ i, IsDiscreteValuationRing (carrier i)

/-- Builds a finite family from its component rings and their structures. -/
def StrictHenselianDvrFamily.ofFamily {m : ℕ}
    (carrier : Fin (m + 1) → Type v)
    (instCommRing : ∀ i, CommRing (carrier i))
    (instStrictHenselian : ∀ i, StrictHenselianLocalRing (carrier i))
    (instDomain : ∀ i, IsDomain (carrier i))
    (instDvr : ∀ i, IsDiscreteValuationRing (carrier i)) :
    StrictHenselianDvrFamily.{v} m :=
  { carrier := carrier
    instCommRing := instCommRing
    instStrictHenselian := instStrictHenselian
    instDomain := instDomain
    instDvr := instDvr }

/-- A local ring is a wedge of a strictly henselian DVR family when it is
isomorphic to the compatible-residue subring of the family's product. -/
def StrictHenselianDvrFamily.IsWedgeOf
    {m : ℕ} (As : StrictHenselianDvrFamily.{v} m)
    (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  @LocalRing.Wedge.IsWedgeOf m A _ _ As.carrier As.instCommRing
    (fun i ↦ (As.instStrictHenselian i).toIsLocalRing)

end LocalRing.Wedge
