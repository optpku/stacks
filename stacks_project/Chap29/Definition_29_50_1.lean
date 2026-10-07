module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Definition 29.50.1: for schemes with finitely many irreducible components, a morphism is
birational exactly when it bijects their generic points and induces an isomorphism on the stalk
at every generic point of the source. -/
@[stacks 01RO] #check
  (AlgebraicGeometry.isBirational_iff_of_finiteIrreducibleComponents :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}}
      [Finite (irreducibleComponents X)]
      [Finite (irreducibleComponents Y)] (f : X ⟶ Y),
      AlgebraicGeometry.IsBirational f ↔
        Set.BijOn f.base X⁰ Y⁰ ∧
          ∀ {η : X}, η ∈ X⁰ → IsIso (f.stalkMap η))
