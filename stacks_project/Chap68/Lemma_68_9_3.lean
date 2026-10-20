module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Finite
import StacksCheckRecall

/-!
# Integral scheme covers finite étale over a dense open

A quasi-compact quasi-separated algebraic space whose points space has finitely
many irreducible components admits a surjective integral morphism from a scheme
that is finite étale over a quasi-compact dense open. Given a surjective étale
cover, the morphism may be chosen to factor Zariski-locally through that cover.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.9.3 (1): Existence of the cover. -/
@[stacks 0GUL] #check
  (AlgebraicGeometry.AlgebraicSpace.IntegralCover.exists_finiteEtale_dense :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasFiniteIrreducibleComponents X],
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (U : OpenSubspace X),
      IsScheme Y ∧ IsIntegralHom f ∧ Surjective f ∧
        IsQuasiCompact U.X ∧ Dense U.pointsSet ∧
          IsFinite (CategoryTheory.Limits.pullback.snd (C := AlgebraicSpace S) f U.ι) ∧
            Etale (CategoryTheory.Limits.pullback.snd (C := AlgebraicSpace S) f U.ι))

/- Lemma 68.9.3 (2): Local factorization through a prescribed surjective étale cover. -/
@[stacks 0GUL] #check
  (AlgebraicGeometry.AlgebraicSpace.IntegralCover.exists_finiteEtale_dense_locallyFactorsThrough :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasFiniteIrreducibleComponents X]
    {V : AlgebraicSpace S} (v : V ⟶ X) [Surjective v] [Etale v],
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (U : OpenSubspace X),
      IsScheme Y ∧ IsIntegralHom f ∧ Surjective f ∧
        IsQuasiCompact U.X ∧ Dense U.pointsSet ∧
          IsFinite (CategoryTheory.Limits.pullback.snd (C := AlgebraicSpace S) f U.ι) ∧
            Etale (CategoryTheory.Limits.pullback.snd (C := AlgebraicSpace S) f U.ι) ∧
              zariskiLocallyFactorsThrough f v)

end AlgebraicGeometry.AlgebraicSpace
