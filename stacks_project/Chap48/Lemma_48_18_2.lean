module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Etale
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 48.18.2: for an etale morphism of finite-type separated schemes over a
Noetherian base, every bounded-below upper-shriek model is naturally isomorphic to
bounded-below derived pullback. -/
@[stacks 0FWI] #check (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.isomorphic_pullback_of_etale :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]
      {X Y : AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S}
      (f : X ⟶ Y) [AlgebraicGeometry.Etale f.hom.left]
      (P : AlgebraicGeometry.Scheme.Compactification.Of Y.obj.left
        (CategoryTheory.Over.mk f.hom.left))
      (A : AlgebraicGeometry.Scheme.DerivedQCoh.PlusRightAdjoint
        (AlgebraicGeometry.Scheme.Compactification.Of.ambientMorphism P)),
      CategoryTheory.IsIsomorphic
        (AlgebraicGeometry.Scheme.Compactification.Of.upperShriek f P A.plus)
        (AlgebraicGeometry.Scheme.DerivedQCoh.Flat.pullbackPlus f.hom.left))
