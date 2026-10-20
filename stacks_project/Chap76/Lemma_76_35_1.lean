module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.Characterization
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.35.1: Characterizations of finite morphisms of algebraic spaces. -/
@[stacks 0A4X]
#check (AlgebraicGeometry.AlgebraicSpace.IsFinite.proper_discreteFieldFibers_tfae :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE
      [ IsFinite f
      , Proper f ∧ LocallyQuasiFinite f
      , Proper f ∧ discreteFieldFibers f
      , UniversallyClosed f ∧ Separated f ∧ LocallyOfFiniteType f ∧
          discreteFieldFibers f ])
