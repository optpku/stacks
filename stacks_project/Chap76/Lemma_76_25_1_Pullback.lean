module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Pullback
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra

/-!
# Pullback of quasi-coherent algebras on algebraic spaces

The pullback functor is provided by its mathematical owner. The inverse-image structure
map is also available under its original name for existing consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

/-- The inverse-image structure map of a morphism of algebraic spaces. -/
abbrev inverseImageStructure {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (pullbackSheafFunctor f).obj (commStructureSheaf X) ⟶ commStructureSheaf Y :=
  AlgebraicSpace.commInverseImageStructureSheafMap f

#check (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.pullback :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X),
    X.QcAlgebraUnder ⥤ Y.QcAlgebraUnder)

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
