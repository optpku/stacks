module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ZariskiLocalFactorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Integral scheme covers of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact, absolutely quasi-separated algebraic space has an
integral scheme cover that factors Zariski-locally through any given
surjective étale morphism. -/
theorem exists_surjective_isIntegralHom_isScheme_locallyFactorsThrough
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {U : AlgebraicSpace S} (u : U ⟶ X) [Surjective u] [Etale u] :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsScheme Y ∧ IsIntegralHom f ∧ Surjective f ∧
        zariskiLocallyFactorsThrough f u := by
  sorry

/-- A quasi-compact, absolutely quasi-separated algebraic space admits a
surjective integral morphism from a scheme. -/
theorem exists_surjective_isIntegralHom_isScheme {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsScheme Y ∧ IsIntegralHom f ∧ Surjective f := by
  obtain ⟨Y, f, hY, hIntegral, hSurjective, _⟩ :=
    exists_surjective_isIntegralHom_isScheme_locallyFactorsThrough X (𝟙 X)
  exact ⟨Y, f, hY, hIntegral, hSurjective⟩

namespace IntegralCover

/-- A quasi-compact, absolutely quasi-separated algebraic space with finitely many
irreducible components admits a surjective integral scheme cover, finite étale
over a quasi-compact dense open, that factors Zariski-locally through any given
surjective étale morphism. -/
theorem exists_finiteEtale_dense_locallyFactorsThrough
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasFiniteIrreducibleComponents X]
    {V : AlgebraicSpace S} (v : V ⟶ X) [Surjective v] [Etale v] :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (U : OpenSubspace X),
      IsScheme Y ∧ IsIntegralHom f ∧ Surjective f ∧
        IsQuasiCompact U.X ∧ Dense U.pointsSet ∧
          IsFinite (CategoryTheory.Limits.pullback.snd (C := AlgebraicSpace S) f U.ι) ∧
            Etale (CategoryTheory.Limits.pullback.snd (C := AlgebraicSpace S) f U.ι) ∧
              zariskiLocallyFactorsThrough f v := by
  sorry

/-- A quasi-compact, absolutely quasi-separated algebraic space with finitely many
irreducible components admits a surjective integral scheme cover that is finite
étale over a quasi-compact dense open. -/
theorem exists_finiteEtale_dense
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasFiniteIrreducibleComponents X] :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (U : OpenSubspace X),
      IsScheme Y ∧ IsIntegralHom f ∧ Surjective f ∧
        IsQuasiCompact U.X ∧ Dense U.pointsSet ∧
          IsFinite (CategoryTheory.Limits.pullback.snd (C := AlgebraicSpace S) f U.ι) ∧
            Etale (CategoryTheory.Limits.pullback.snd (C := AlgebraicSpace S) f U.ι) := by
  obtain ⟨Y, f, U, hY, hIntegral, hSurjective, hQuasiCompact, hDense, hFinite, hEtale, _⟩ :=
    exists_finiteEtale_dense_locallyFactorsThrough X (𝟙 X)
  exact ⟨Y, f, U, hY, hIntegral, hSurjective, hQuasiCompact, hDense, hFinite, hEtale⟩

end IntegralCover

end AlgebraicGeometry.AlgebraicSpace
