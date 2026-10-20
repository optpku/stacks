module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap75.Lemma_75_26_4_VectorBundle
public import stacks_project.Chap76.Lemma_76_27_3_Gorenstein
public import stacks_project.Chap86.Definition_86_9_1_RelativeDualizing
public import stacks_project.Chap109.Lemma_109_3_1_Family

/-!
# Relative dualizing sheaf of a Gorenstein family of curves

For a family of curves with Gorenstein fibres equidimensional of dimension 1,
the degree `-1` cohomology sheaf of a relative dualizing complex is an
invertible `𝒪_X`-module, and its formation commutes with arbitrary base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex

variable {S : Scheme.{u}}



/-- Lemma 109.19.3 (1): for a family of curves `f : X ⟶ Y` with Gorenstein fibres
equidimensional of dimension 1, the relative dualizing sheaf
`cohomologySheaf C.complex (-1)` is an invertible `𝒪_X`-module. -/
@[stacks 0E6R]
instance instIsInvertibleObject_cohomologySheaf     {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [Gorenstein f]
    [RelativeDimension f 1] (C : RelativeDualizingComplex f) :
    isInvertibleObject (cohomologySheaf C.complex (-1)) :=
  sorry

/-- Lemma 109.19.3 (2): formation of the relative dualizing sheaf of a Gorenstein
family of curves of relative dimension 1 commutes with arbitrary base change. -/
@[stacks 0E6R]
theorem cohomologySheaf_baseChange_of_gorenstein     {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [Gorenstein f]
    [RelativeDimension f 1] (C : RelativeDualizingComplex f)
    {X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    [∀ sq : EtaleSquare f',
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f',
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] (g : Y' ⟶ Y)
    [IsFamily f'] [Gorenstein f'] [RelativeDimension f' 1]
    (sq : IsPullback g' f' f g) (C' : RelativeDualizingComplex f') :
    IsIsomorphic
      ((Modules.pullback g').obj (cohomologySheaf C.complex (-1)))
      (cohomologySheaf C'.complex (-1)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
