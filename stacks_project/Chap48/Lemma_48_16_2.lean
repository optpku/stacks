module

public import stacks_project.Chap48.Lemma_48_16_2_Instances
public import stacks_project.Chap48.Lemma_48_16_2_Comparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.16.2: for a morphism `f : X ⟶ Y` in
`Scheme.FiniteTypeSeparatedOver S`, the bounded-below upper-shriek functor is independent,
up to canonical isomorphism, of the choice of compactification. -/
@[stacks 0AA0] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.upperShriek_independent :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [IsNoetherian S]
      {X Y : AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
      (a : (P : AlgebraicGeometry.Scheme.Compactification.Of Y.obj.left
        (Over.mk f.hom.left)) →
          AlgebraicGeometry.Scheme.DerivedQCoh Y.obj.left ⥤
            AlgebraicGeometry.Scheme.DerivedQCoh P.obj.right.left)
      (aAdjunction : ∀ P : AlgebraicGeometry.Scheme.Compactification.Of Y.obj.left
        (Over.mk f.hom.left),
          AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn
              P.obj.right.hom ⊣ a P)
      (aPlus : (P : AlgebraicGeometry.Scheme.Compactification.Of Y.obj.left
        (Over.mk f.hom.left)) →
          AlgebraicGeometry.Scheme.DerivedQCoh.Plus Y.obj.left ⥤
            AlgebraicGeometry.Scheme.DerivedQCoh.Plus P.obj.right.left)
      (aPlusCompatibility : ∀ P : AlgebraicGeometry.Scheme.Compactification.Of
        Y.obj.left (Over.mk f.hom.left),
          aPlus P ⋙ CategoryTheory.DerivedCategory.Plus.CohomologyIn.ambient
              (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty
                P.obj.right.left.toRingedSpace) ≅
            CategoryTheory.DerivedCategory.Plus.CohomologyIn.toUnbounded
                (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty
                  Y.obj.left.toRingedSpace) ⋙
              a P ⋙ AlgebraicGeometry.Scheme.DerivedQCoh.inclusion P.obj.right.left)
      (P Q : AlgebraicGeometry.Scheme.Compactification.Of Y.obj.left
        (Over.mk f.hom.left)),
      IsIsomorphic
        (AlgebraicGeometry.Scheme.Compactification.Of.upperShriek f P (aPlus P))
        (AlgebraicGeometry.Scheme.Compactification.Of.upperShriek f Q (aPlus Q)))
