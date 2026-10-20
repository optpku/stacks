module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.ClosedImmersion
import StacksCheckRecall

/-!
# Finite presentation of closed immersions of algebraic spaces

A closed immersion of algebraic spaces is of finite presentation exactly when
its associated kernel ideal sheaf is of finite type as an `𝒪_X`-module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.28.12: A closed immersion `i : Z ⟶ X` of algebraic spaces is of
finite presentation if and only if the associated quasi-coherent sheaf of
ideals `I = Ker(𝒪_X ⟶ i_* 𝒪_Z)` is of finite type as an `𝒪_X`-module. -/
@[stacks 084Q] #check
  (AlgebraicGeometry.AlgebraicSpace.finitePresentation_iff_idealSheaf_isFiniteType :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X),
      [AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion i] →
        (AlgebraicGeometry.AlgebraicSpace.FinitePresentation i ↔
          SheafOfModules.IsFiniteType
            (AlgebraicGeometry.AlgebraicSpace.Hom.idealSheaf i)))
