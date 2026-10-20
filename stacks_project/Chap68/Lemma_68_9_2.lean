module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Integral
import StacksCheckRecall

/-!
# Integral scheme covers of quasi-compact quasi-separated algebraic spaces

A quasi-compact quasi-separated algebraic space admits a surjective integral
morphism from a scheme, which may be chosen to factor Zariski-locally through
any given surjective étale morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.9.2 (2): Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Given a surjective étale morphism
`U ⟶ X` we may choose a surjective integral morphism `Y ⟶ X` with `Y` a scheme
such that for every `y ∈ Y` there is an open neighbourhood `V ⊂ Y` such that
`V ⟶ X` factors through `U`. -/
@[stacks 09YB] #check (AlgebraicGeometry.AlgebraicSpace.exists_surjective_isIntegralHom_isScheme_locallyFactorsThrough :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    {U : AlgebraicSpace S} (u : U ⟶ X) [Surjective u] [Etale u],
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsScheme Y ∧ IsIntegralHom f ∧ Surjective f ∧
        zariskiLocallyFactorsThrough f u)

/- Lemma 68.9.2 (1): A quasi-compact, absolutely quasi-separated algebraic
space over a scheme admits a surjective integral morphism from a scheme. -/
@[stacks 09YB] #check (AlgebraicGeometry.AlgebraicSpace.exists_surjective_isIntegralHom_isScheme :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X],
    ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X),
      IsScheme Y ∧ IsIntegralHom f ∧ Surjective f)
