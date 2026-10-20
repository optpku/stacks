module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Finite
import StacksCheckRecall

/-!
# Finite scheme covers of quasi-compact quasi-separated algebraic spaces

A quasi-compact quasi-separated algebraic space admits a surjective finite
morphism of finite presentation from a scheme, which may be chosen to factor
Zariski-locally through any given surjective étale morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Proposition 70.16.1 (1): Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. There exists a surjective finite
morphism `Y ⟶ X` of finite presentation where `Y` is a scheme. -/
@[stacks 09YC] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_surjective_isFinite_finitePresentation_isScheme :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X],
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsScheme Y ∧ IsFinite f ∧ FinitePresentation f ∧ Surjective f)

/- Proposition 70.16.1 (2): Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Given a surjective étale morphism
`U ⟶ X` we may choose a surjective finite morphism `Y ⟶ X` of finite
presentation with `Y` a scheme such that for every `y ∈ Y` there is an open
neighbourhood `V ⊂ Y` such that `V ⟶ X` factors through `U`. -/
@[stacks 09YC] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteCover.exists_scheme_locallyFactorsThrough :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      {U : AlgebraicSpace S} (u : U ⟶ X) [Surjective u] [Etale u],
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsScheme Y ∧ IsFinite f ∧ FinitePresentation f ∧ Surjective f ∧
        zariskiLocallyFactorsThrough f u)

end AlgebraicGeometry.AlgebraicSpace
