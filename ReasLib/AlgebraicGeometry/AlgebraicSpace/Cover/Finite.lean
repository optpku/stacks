module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Finite scheme covers of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact, absolutely quasi-separated algebraic space over a scheme
admits a surjective finite morphism of finite presentation from a scheme. -/
theorem exists_surjective_isFinite_finitePresentation_isScheme
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsScheme Y ∧ IsFinite f ∧ FinitePresentation f ∧ Surjective f :=
  sorry

/-- A quasi-compact, absolutely quasi-separated algebraic space admits a
surjective finite scheme cover of finite presentation that factors
Zariski-locally through any prescribed surjective étale morphism. -/
theorem FiniteCover.exists_scheme_locallyFactorsThrough
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {U : AlgebraicSpace S} (u : U ⟶ X) [Surjective u] [Etale u] :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsScheme Y ∧ IsFinite f ∧ FinitePresentation f ∧ Surjective f ∧
        zariskiLocallyFactorsThrough f u :=
  sorry

namespace FiniteCover

/-- A quasi-compact, absolutely quasi-separated algebraic space with finitely many
irreducible components admits a surjective finite scheme cover of finite
presentation, finite étale over a quasi-compact dense open, that factors
Zariski-locally through any given surjective étale morphism. -/
theorem exists_finiteEtale_dense_locallyFactorsThrough
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasFiniteIrreducibleComponents X]
    {V : AlgebraicSpace S} (v : V ⟶ X) [Surjective v] [Etale v] :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (U : OpenSubspace X),
      IsScheme Y ∧ IsFinite f ∧ FinitePresentation f ∧ Surjective f ∧
        IsQuasiCompact U.X ∧ Dense U.pointsSet ∧
          IsFinite (CategoryTheory.Limits.pullback.snd (C := AlgebraicSpace S) f U.ι) ∧
            Etale (CategoryTheory.Limits.pullback.snd (C := AlgebraicSpace S) f U.ι) ∧
              zariskiLocallyFactorsThrough f v := by
  sorry

/-- A quasi-compact, absolutely quasi-separated algebraic space with finitely many
irreducible components admits a surjective finite scheme cover of finite
presentation that is finite étale over a quasi-compact dense open. -/
theorem exists_finiteEtale_dense
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasFiniteIrreducibleComponents X] :
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (U : OpenSubspace X),
      IsScheme Y ∧ IsFinite f ∧ FinitePresentation f ∧ Surjective f ∧
        IsQuasiCompact U.X ∧ Dense U.pointsSet ∧
          IsFinite (CategoryTheory.Limits.pullback.snd (C := AlgebraicSpace S) f U.ι) ∧
            Etale (CategoryTheory.Limits.pullback.snd (C := AlgebraicSpace S) f U.ι) := by
  obtain ⟨Y, f, U, hY, hFinite, hPresentation, hSurjective, hQuasiCompact, hDense, hFiniteOpen, hEtale, _⟩ :=
    exists_finiteEtale_dense_locallyFactorsThrough X (𝟙 X)
  exact ⟨Y, f, U, hY, hFinite, hPresentation, hSurjective, hQuasiCompact, hDense, hFiniteOpen, hEtale⟩

end FiniteCover

end AlgebraicGeometry.AlgebraicSpace
