module

public import Mathlib.AlgebraicGeometry.Stalk
public import ReasLib.RingTheory.Henselian.Henselization

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Henselization

/-- The canonical morphism from the spectrum of a chosen henselization of the stalk at
`s` to `S`. -/
noncomputable def map.{u} (S : Scheme.{u}) (s : S) (Rh : Type u) [CommRing Rh]
    [Algebra (S.presheaf.stalk s) Rh] [IsHenselizationOf (S.presheaf.stalk s) Rh] :
    Spec (CommRingCat.of Rh) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) Rh)) ≫
    S.fromSpecStalk s

/-- The canonical henselization morphism sends the closed point to the point of the
original scheme whose stalk was henselized. -/
theorem map_closedPoint (S : Scheme.{u}) (s : S) (Rh : Type u) [CommRing Rh]
    [Algebra (S.presheaf.stalk s) Rh] [IsHenselizationOf (S.presheaf.stalk s) Rh] :
    map S s Rh (IsLocalRing.closedPoint Rh) = s := sorry

end AlgebraicGeometry.Scheme.Henselization
