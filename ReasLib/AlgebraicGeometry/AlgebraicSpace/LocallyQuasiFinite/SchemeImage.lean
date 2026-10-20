module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The image of a quasi-affine open subspace in an étale affine base change of a
separated morphism that is locally of finite type and locally quasi-finite is a
quasi-compact open subspace representable by a scheme. -/
theorem exists_quasiCompact_scheme_image {S : Scheme.{u}}
    {T T' X P : AlgebraicSpace S} {h : T' ⟶ T} {f : X ⟶ T}
    {pT' : P ⟶ T'} {pX : P ⟶ X} (V' : OpenSubspace P)
    [IsAffine T] [IsAffine T'] [Etale h] [Separated f]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (hpb : IsPullback pT' pX h f) [QuasiAffine (V'.ι ≫ pT')] :
    ∃ U : OpenSubspace X,
      U.pointsSet = Set.range (Points.map (V'.ι ≫ pX)) ∧
        IsQuasiCompact U.X ∧ IsScheme U.X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
