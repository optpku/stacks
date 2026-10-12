/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Unramified
public import ReasLib.RingTheory.Etale.LocalRing

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finite-type morphism to a locally Noetherian scheme is étale at a point
if and only if its induced homomorphism on local rings is essentially étale. -/
theorem etaleAt_iff_stalkMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    (x : X) :
    f.EtaleAt x ↔ (f.stalkMap x).hom.EssEtale := sorry

end AlgebraicGeometry.Scheme.Hom
