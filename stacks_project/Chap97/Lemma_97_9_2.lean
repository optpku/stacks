module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SpaceOfSections
import StacksCheckRecall

/-!
# Spaces of sections of étale morphisms onto finite locally free schemes

If `π : Z ⟶ U` is finite locally free and `W ⟶ Z` is étale, the functor of
sections of `W_T ⟶ Z_T` is an algebraic space étale over `U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 97.9.2. For a finite locally free morphism `Z ⟶ U` and an étale morphism
`W ⟶ Z`, the section functor is an algebraic space étale over `U`. -/
@[stacks 05XR] #check
  (AlgebraicGeometry.AlgebraicSpace.SpaceOfSections.isAlgebraicSpace_etale :
    ∀ {U Z : Scheme.{u}} {W : AlgebraicSpace U} (π : Z ⟶ U)
      (f : W ⟶ ofOver (Over.mk π)) [IsFiniteLocallyFree π] [Etale f],
      IsAlgebraicSpace (SpaceOfSections.functor π f) ∧
        Etale (SchemeRealization.toBase (SpaceOfSections.space π f)))

