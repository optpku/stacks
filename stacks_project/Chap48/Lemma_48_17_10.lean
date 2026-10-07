module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Flat
public import stacks_project.Chap48.Lemma_48_17_10_Instances
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification
open AlgebraicGeometry.Scheme.Compactification.Of
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat

noncomputable section

universe u

/- Lemma 48.17.10 (1) -/
@[stacks 0E9T] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.dualizingObject_isPerfectRelativeTo_of_flat :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
      (P : AlgebraicGeometry.Scheme.Compactification.Of
        Y.obj.left (Over.mk f.hom.left))
      (A : DerivedQCoh.PlusRightAdjoint
        (AlgebraicGeometry.Scheme.Compactification.Of.ambientMorphism P)),
      ModuleDerived.IsPerfectRelativeTo f.hom.left
        (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.dualizingObject f P A).obj)

/- Lemma 48.17.10 (2) -/
@[stacks 0E9T] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.dualizingHomothety_isIso_of_flat :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Flat f.hom.left]
      (P : AlgebraicGeometry.Scheme.Compactification.Of
        Y.obj.left (Over.mk f.hom.left))
      (A : DerivedQCoh.PlusRightAdjoint
        (AlgebraicGeometry.Scheme.Compactification.Of.ambientMorphism P))
      [HomotopyTensorDescends (X.obj.left).toRingedSpace]
      [TensorDescends (X.obj.left).toRingedSpace]
      [IsLocalization (X.obj.left).toRingedSpace]
      (H_X : MonoidalClosed (RingedSpace.ModuleDerived (X.obj.left).toRingedSpace)),
      IsIso (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.dualizingHomothety
        f P A H_X))
