/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Unramified

/-- A finite unramified morphism with a singleton fibre and purely inseparable residue-field
extension restricts to a closed immersion over an open neighbourhood of the image point. -/
theorem exists_isClosedImmersion_morphismRestrict
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Unramified f]
    (s : S) (x : X) (hxs : f x = s)
    (h_fiber : f ⁻¹' ({s} : Set S) = {x})
    (hκ : ((Scheme.residueFieldCongr hxs).inv ≫
      f.residueFieldMap x).hom.IsPurelyInseparable) :
    ∃ U : S.Opens, s ∈ U ∧ IsClosedImmersion (f ∣_ U) := sorry

end AlgebraicGeometry.Unramified
