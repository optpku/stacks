/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.Bounded.Map
public import ReasLib.Algebra.Module.Flat.Relative
public import ReasLib.Algebra.Homology.CochainComplex.Cokernel.Restriction
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.FlatCokernel
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative flat boundary cokernels

The ring-homomorphism statements are the canonical relative owners.  Their conclusions use
`Module.FlatAlong`, while the algebra versions are thin specializations along `algebraMap`; the
explicit restricted-module presentation is available through the termwise and cokernel
restriction comparisons when a categorical proof needs it.
@stack 0653
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.DerivedCategory.FlatCokernel

variable {R A : Type u} [CommRing R] [CommRing A]

/-- Stacks `0653` and `0E1U`: a lower Tor-amplitude bound along `sigma` makes the incoming differential cokernel
flat along the source ring. -/
@[stacks 0653 "relative flat differential cokernel from a lower Tor bound",
  stacks 0E1U "flat truncation boundary along a ring map"]
theorem ofTorAmplitudeGEAlong_cokernel
    (sigma : R →+* A) (E : CochainComplex (ModuleCat A) ℤ) (a : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat A) E)
    (hFlat : E.IsTermwiseFlatAlong sigma)
    (hTor : (DerivedCategory.Q.obj E).HasTorAmplitudeGEAlong sigma a) :
    Module.FlatAlong sigma (E.differentialCokernel a) := sorry
/- Proof strategy: apply `ofTorAmplitudeGE_cokernel` to `E.restrictScalarsAlong sigma`, using
`Functor.mapDerivedCategoryFactors` to transport the Tor bound and degreewise restriction to
transport boundedness.  Then identify the restricted action with `Module.FlatAlong`. -/

/-- Stacks `0653` and `0E1U`: a lower Tor-amplitude bound along `sigma` makes the canonical opcycles flat along the
source ring. -/
@[stacks 0653 "relative flat opcycles from a lower Tor bound",
  stacks 0E1U "flat truncation opcycles along a ring map"]
theorem ofTorAmplitudeGEAlong
    (sigma : R →+* A) (E : CochainComplex (ModuleCat A) ℤ) (a : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat A) E)
    (hFlat : E.IsTermwiseFlatAlong sigma)
    (hTor : (DerivedCategory.Q.obj E).HasTorAmplitudeGEAlong sigma a) :
    Module.FlatAlong sigma (E.opcycles a) := sorry
/- Proof strategy: obtain relative flatness of `E.differentialCokernel a` from
`ofTorAmplitudeGEAlong_cokernel`, then transport it across `E.opcyclesIsoCokernel a` and the
restriction-of-scalars comparison for opcycles. -/

/-- Stacks `0653` and `0E1U`: Tor amplitude in `[a, b]` along `sigma` makes the boundary cokernel in degree `a`
flat along the source ring. -/
@[stacks 0653 "relative flat differential cokernel from finite Tor amplitude",
  stacks 0E1U "flat truncation boundary from relative Tor amplitude"]
theorem ofTorAmplitudeInAlong_cokernel
    (sigma : R →+* A) (E : CochainComplex (ModuleCat A) ℤ) (a b : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat A) E)
    (hFlat : E.IsTermwiseFlatAlong sigma)
    (hTor : (DerivedCategory.Q.obj E).HasTorAmplitudeInAlong sigma a b) :
    Module.FlatAlong sigma (E.differentialCokernel a) := sorry
/- Proof strategy: extract `HasTorAmplitudeGEAlong sigma a` from `hTor` and apply
`ofTorAmplitudeGEAlong_cokernel`. -/

/-- Stacks `0653` and `0E1U`: Tor amplitude in `[a, b]` along `sigma` makes the canonical opcycles flat along the
source ring. -/
@[stacks 0653 "relative flat opcycles from finite Tor amplitude",
  stacks 0E1U "flat truncation opcycles from relative Tor amplitude"]
theorem ofTorAmplitudeInAlong
    (sigma : R →+* A) (E : CochainComplex (ModuleCat A) ℤ) (a b : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat A) E)
    (hFlat : E.IsTermwiseFlatAlong sigma)
    (hTor : (DerivedCategory.Q.obj E).HasTorAmplitudeInAlong sigma a b) :
    Module.FlatAlong sigma (E.opcycles a) := sorry
/- Proof strategy: extract `HasTorAmplitudeGEAlong sigma a` from `hTor` and apply
`ofTorAmplitudeGEAlong`. -/

/-- Stacks `0653` and `0E1U`: over a base algebra, a lower relative Tor-amplitude bound makes the incoming
differential cokernel flat along the base algebra map. -/
@[stacks 0653 "flat differential cokernel over a base from a lower Tor bound",
  stacks 0E1U "flat truncation boundary over a base"]
theorem ofTorAmplitudeGEOver_cokernel
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (E : CochainComplex (ModuleCat A) ℤ) (a : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat A) E)
    (hFlat : E.IsTermwiseFlatOver R)
    (hTor : (DerivedCategory.Q.obj E).HasTorAmplitudeGEOver R a) :
    Module.FlatAlong (algebraMap R A) (E.differentialCokernel a) := sorry
/- Proof strategy: specialize `ofTorAmplitudeGEAlong_cokernel` to `algebraMap R A`. -/

/-- Stacks `0653` and `0E1U`: over a base algebra, a lower relative Tor-amplitude bound makes the canonical
opcycles flat along the base algebra map. -/
@[stacks 0653 "flat opcycles over a base from a lower Tor bound",
  stacks 0E1U "flat truncation opcycles over a base"]
theorem ofTorAmplitudeGEOver
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (E : CochainComplex (ModuleCat A) ℤ) (a : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat A) E)
    (hFlat : E.IsTermwiseFlatOver R)
    (hTor : (DerivedCategory.Q.obj E).HasTorAmplitudeGEOver R a) :
    Module.FlatAlong (algebraMap R A) (E.opcycles a) := sorry
/- Proof strategy: specialize `ofTorAmplitudeGEAlong` to `algebraMap R A`. -/

/-- Stacks `0653` and `0E1U`: over a base algebra, relative Tor amplitude in `[a, b]` makes the boundary
cokernel in degree `a` flat along the base algebra map. -/
@[stacks 0653 "flat differential cokernel over a base from finite Tor amplitude",
  stacks 0E1U "flat truncation boundary from Tor amplitude over a base"]
theorem ofTorAmplitudeInOver_cokernel
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (E : CochainComplex (ModuleCat A) ℤ) (a b : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat A) E)
    (hFlat : E.IsTermwiseFlatOver R)
    (hTor : (DerivedCategory.Q.obj E).HasTorAmplitudeInOver R a b) :
    Module.FlatAlong (algebraMap R A) (E.differentialCokernel a) := sorry
/- Proof strategy: specialize `ofTorAmplitudeInAlong_cokernel` to `algebraMap R A`. -/

/-- Stacks `0653` and `0E1U`: over a base algebra, relative Tor amplitude in `[a, b]` makes the canonical opcycles
flat along the base algebra map. -/
@[stacks 0653 "flat opcycles over a base from finite Tor amplitude",
  stacks 0E1U "flat truncation opcycles from Tor amplitude over a base"]
theorem ofTorAmplitudeInOver
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (E : CochainComplex (ModuleCat A) ℤ) (a b : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat A) E)
    (hFlat : E.IsTermwiseFlatOver R)
    (hTor : (DerivedCategory.Q.obj E).HasTorAmplitudeInOver R a b) :
    Module.FlatAlong (algebraMap R A) (E.opcycles a) := sorry
/- Proof strategy: specialize `ofTorAmplitudeInAlong` to `algebraMap R A`. -/

end CategoryTheory.DerivedCategory.FlatCokernel
