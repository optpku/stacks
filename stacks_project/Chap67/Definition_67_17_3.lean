module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticClosure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 67.17.3 (1): the scheme-theoretic closure of an open subspace `U`
of an algebraic space `X` over a scheme `S` is the scheme-theoretic image of the
open immersion `U ⟶ X`. -/
@[stacks 0834] #check (AlgebraicGeometry.AlgebraicSpace.Open.isSchemeTheoreticClosure_iff :
  ∀ {S : Scheme.{u}} {X U Z : AlgebraicSpace S} (j : U ⟶ X)
    [AlgebraicSpace.IsOpenImmersion j] (toClosure : U ⟶ Z) (i : Z ⟶ X),
    AlgebraicSpace.Open.IsSchemeTheoreticClosure j toClosure i ↔
      AlgebraicSpace.IsSchemeTheoreticImage j toClosure i)

/- Definition 67.17.3 (2): an open subspace `U` of an algebraic space `X` over a
scheme `S` is scheme-theoretically dense in `X` if the equivalent conditions of
Lemma 67.17.2 are satisfied. -/
@[stacks 0834] #check (AlgebraicGeometry.AlgebraicSpace.Open.isSchemeTheoreticallyDense_iff_forallEtale :
  ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X)
    [AlgebraicSpace.IsOpenImmersion ι],
    AlgebraicSpace.Open.IsSchemeTheoreticallyDense ι ↔
      AlgebraicSpace.SchemeTheoreticDensity.forallEtale ι)
