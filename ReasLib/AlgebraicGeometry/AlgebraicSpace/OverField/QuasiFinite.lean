module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OverField.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OverField.DimensionZero
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme

/-!
# Locally quasi-finite algebraic spaces over a field

Local finite type and local quasi-finiteness over a field characterize schemes
of dimension at most zero and coproducts of spectra of finite-dimensional
local Artinian algebras.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space locally of finite type and locally quasi-finite over a
field is a scheme. -/
instance isScheme_of_locallyQuasiFinite {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType (SchemeRealization.toBase X)]
    [LocallyQuasiFinite (SchemeRealization.toBase X)] :
    IsScheme X :=
  sorry

/-- An algebraic space over a field is locally of finite type and locally
quasi-finite if and only if it admits a coproduct presentation by spectra of
finite-dimensional local Artinian algebras over that field. -/
theorem locallyQuasiFinite_iff_finiteLocalArtinianCoproduct {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    LocallyOfFiniteType (SchemeRealization.toBase X) ∧
      LocallyQuasiFinite (SchemeRealization.toBase X) ↔
      Nonempty (FiniteLocalArtinianCoproduct X) :=
  sorry

/-- For an algebraic space over a field, local finite type and local
quasi-finiteness are equivalent to local finite type and dimension at most zero,
to being a scheme with either property, and to a coproduct presentation by
spectra of finite-dimensional local Artinian algebras over that field.
Dimension at most zero includes the empty space, whose dimension is bottom. -/
theorem tfae_locallyQuasiFinite_over_field {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    List.TFAE
      [ LocallyOfFiniteType (SchemeRealization.toBase X) ∧
          LocallyQuasiFinite (SchemeRealization.toBase X)
      , LocallyOfFiniteType (SchemeRealization.toBase X) ∧ dimension X ≤ 0
      , IsScheme X ∧ LocallyOfFiniteType (SchemeRealization.toBase X) ∧
          LocallyQuasiFinite (SchemeRealization.toBase X)
      , IsScheme X ∧ LocallyOfFiniteType (SchemeRealization.toBase X) ∧ dimension X ≤ 0
      , Nonempty (FiniteLocalArtinianCoproduct X) ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
