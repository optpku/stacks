module

public import Mathlib.RingTheory.Artinian.Ring
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Affine morphisms from Artinian spectra

Every morphism from the spectrum of an Artinian ring to an absolutely
quasi-separated algebraic space is affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every morphism over a scheme from the spectrum of an Artinian ring to an
absolutely quasi-separated algebraic space is affine. -/
@[stacks 09TF]
instance Affine.of_artinianSpec {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiSeparated (toSpecZ X)] {A : Type u} [CommRing A] [IsArtinianRing A]
    {σ : Spec (.of A) ⟶ S} (f : ofOver (Over.mk σ) ⟶ X) : Affine f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
