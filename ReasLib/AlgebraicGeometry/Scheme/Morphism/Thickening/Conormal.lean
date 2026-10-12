/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.IsFirstOrderThickening

open Scheme.Hom

/-- For a commutative square between first-order thickenings whose map on the closed
subschemes is flat, flatness of the ambient map together with cartesianness is equivalent
to the canonical conormal comparison being an isomorphism. -/
theorem flat_ambient_and_isPullback_iff_conormalMap_isIso
    {X X' S S' : Scheme.{u}} {iX : X ⟶ X'} {iS : S ⟶ S'}
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iS]
    {f : X ⟶ S} {f' : X' ⟶ S'} [Flat f] (sq : CommSq f iX iS f') :
    (Flat f' ∧ IsPullback f iX iS f') ↔ IsIso (Conormal.map sq) := sorry

end AlgebraicGeometry.IsFirstOrderThickening
