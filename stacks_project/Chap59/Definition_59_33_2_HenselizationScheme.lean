module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization

universe u v

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/- The reusable constructors are owned by `ReasLib.AlgebraicGeometry.Scheme.Henselization`.
The typed checks below preserve this source-facing module as an importable bridge. -/
#check (AlgebraicGeometry.Scheme.strictHenselizationScheme :
    ∀ (S : Scheme.{u}) (s : GeometricPoint S) (Rsh : Type v) [CommRing Rsh]
      [Algebra (S.presheaf.stalk s.image) Rsh]
      [IsStrictHenselizationOf (S.presheaf.stalk s.image) Rsh], Scheme.{v})
#check (AlgebraicGeometry.Scheme.henselizationScheme :
    ∀ (S : Scheme.{u}) (x : S) (Rh : Type v) [CommRing Rh]
      [Algebra (S.presheaf.stalk x) Rh]
      [IsHenselizationOf (S.presheaf.stalk x) Rh], Scheme.{v})
#check (AlgebraicGeometry.Scheme.strictHenselizationAt :
    ∀ (S : Scheme.{u}) (s : GeometricPoint S), Scheme.{u})

end AlgebraicGeometry.Scheme
