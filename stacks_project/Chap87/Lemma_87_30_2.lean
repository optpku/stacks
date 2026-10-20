module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation.BaseChange
import StacksCheckRecall

/-!
# Base change of separation axioms for morphisms of formal algebraic spaces

The base change of a separated or quasi-separated morphism of formal algebraic
spaces by any morphism of formal algebraic spaces is again separated or
quasi-separated, respectively.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

/- Lemma 87.30.2 (1): Separated morphisms of formal algebraic spaces are stable
under base change. -/
@[stacks 0ARP] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.separated_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.FormalAlgebraicSpace.Separated S :
        MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)))

/- Lemma 87.30.2 (2): Quasi-separated morphisms of formal algebraic spaces are
stable under base change. -/
@[stacks 0ARP] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.quasiSeparated_isStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.FormalAlgebraicSpace.QuasiSeparated S :
        MorphismProperty ((Over S)ᵒᵖ ⥤ Type u)))
