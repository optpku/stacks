module

public import ReasLib.RingTheory.RingHom.Perfect.Basic
public import ReasLib.RingTheory.RingHom.TorDimension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Tor dimension for perfect ring maps

The intrinsic polynomial-presentation definition of a perfect ring map is
related here to finite Tor dimension in the canonical ModuleCat derived-tensor
model.

@stack 067H
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace RingHom

/-- Definition 15.83.1: a ring map is perfect exactly when it is pseudo-coherent and its target
has finite Tor dimension as a source module. -/
@[stacks 067H "perfect maps and finite Tor dimension"]
theorem isPerfectRingMap_iff_isPseudoCoherentRingMap_and_hasFiniteTorDimension
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) :
    f.IsPerfectRingMap ↔
      f.IsPseudoCoherentRingMap ∧ f.HasFiniteTorDimension := sorry
/- Proof strategy: this is the source-facing spelling of `RingHom.isPerfectRingMap_iff`; use that
canonical class characterization without unfolding the Tor-dimension model. -/

namespace IsPerfectRingMap

/-- The target of a perfect ring map has finite Tor dimension over its source. -/
theorem hasFiniteTorDimension
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] {f : A →+* B}
    (h : f.IsPerfectRingMap) :
    f.HasFiniteTorDimension := sorry
/- Proof strategy: project `h.finiteTorDimension`, or equivalently the second component of
`RingHom.isPerfectRingMap_iff`. -/

/-- A pseudo-coherent ring map whose target has finite Tor dimension is perfect. -/
theorem of_isPseudoCoherentRingMap_of_hasFiniteTorDimension
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] {f : A →+* B}
    (h_pseudo : f.IsPseudoCoherentRingMap)
    (h_tor : f.HasFiniteTorDimension) :
    f.IsPerfectRingMap := sorry
/- Proof strategy: apply the reverse implication of `RingHom.isPerfectRingMap_iff` to
`⟨h_pseudo, h_tor⟩`. -/

end IsPerfectRingMap

end RingHom

namespace Algebra

/-- An algebra map is perfect exactly when it is pseudo-coherent and its
target regular module has finite Tor dimension over the base. -/
theorem isPerfectRingMap_iff_isPseudoCoherentRingMap_and_hasFiniteTorDimension
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] :
    (algebraMap A B).IsPerfectRingMap ↔
      (algebraMap A B).IsPseudoCoherentRingMap ∧
        (algebraMap A B).HasFiniteTorDimension := sorry
/- Proof strategy: specialize the intrinsic RingHom characterization to `algebraMap A B`; no
change of module or algebra structure is required in this formulation. -/

/-- The target regular module of a perfect algebra map has finite Tor dimension. -/
theorem hasFiniteTorDimension_of_isPerfectRingMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (h : (algebraMap A B).IsPerfectRingMap) :
    (algebraMap A B).HasFiniteTorDimension := sorry
/- Proof strategy: apply `RingHom.IsPerfectRingMap.hasFiniteTorDimension` to the algebra map. -/

end Algebra
