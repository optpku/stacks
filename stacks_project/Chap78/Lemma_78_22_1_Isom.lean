module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.CategoryTheory.Fibered.Stack.Prestack
public import stacks_project.Chap65.Lemma_65_7_1_Product
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap78.Lemma_78_20_2_Atlas

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Isom

/-!
# Morphism presheaves of the groupoid prestack

The canonical relative arrow sheaf identifies the Hom presheaf between images of
scheme-valued points in the groupoid prestack.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupoidAlgebraicSpace

universe u

/- Lemma 78.22.1: the identification before stackification. -/
#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.presheafHom_preQuotient_isIsomorphic_isomPullback :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left),
    IsIsomorphic
      ((Functor.fiberPseudofunctor (preQuotient G).p).presheafHom
        (((atlasToPreQuotient G).fiberFunctor S').obj (objOfHom x'))
        (((atlasToPreQuotient G).fiberFunctor S').obj (objOfHom y')))
      (isomPullbackSheaf G x' y').obj)
