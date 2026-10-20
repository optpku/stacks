module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings.NormalizationConfiguration
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.J2
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Henselization
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Nagata
public import ReasLib.RingTheory.Henselian.Henselization.Regular

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- On a locally Noetherian J-2 or Nagata scheme, a closed subscheme is a normal crossings
divisor if and only if its pullback to every strict henselization at a point of its support is a
strict normal crossings divisor. -/
theorem isNormalCrossingsDivisor_iff_strictHenselization
    {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hX : Scheme.IsJ2 X ∨ Scheme.Nagata X) :
    IsNormalCrossingsDivisor D ↔
      ∀ p : X, p ∈ D.support →
        ∀ (Rsh : Type u) [CommRing Rsh] [Algebra (X.presheaf.stalk p) Rsh]
          [IsStrictHenselizationOf (X.presheaf.stalk p) Rsh],
          -- Local instance justification (search instability): Rsh does not determine its base stalk.
          letI : IsNoetherianRing Rsh :=
            @IsStrictHenselizationOf.isNoetherianRing
              (X.presheaf.stalk p) _ _ Rsh _ _ _ _
          let g : Spec (CommRingCat.of Rsh) ⟶ X :=
            Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk p) Rsh)) ≫
              X.fromSpecStalk p
          IsStrictNormalCrossingsDivisor (D.comap g) := sorry

end AlgebraicGeometry
