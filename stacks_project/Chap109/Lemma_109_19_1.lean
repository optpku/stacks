module

public import ReasLib.AlgebraicGeometry.Scheme.Module.StalkFlatness
public import stacks_project.Chap66.Definition_66_18_9_Square
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_26_4_VectorBundle
public import stacks_project.Chap76.Lemma_76_26_3_CohenMacaulay
public import stacks_project.Chap86.Definition_86_9_1_RelativeDualizing
public import stacks_project.Chap109.Lemma_109_3_1_Family

/-!
# Relative dualizing complexes of Cohen–Macaulay families of curves

For a family of curves with Cohen–Macaulay fibres equidimensional of dimension
1, the relative dualizing complex is the shift of its degree `-1` cohomology
sheaf, and that sheaf is pseudo-coherent, flat over the base, and compatible
with arbitrary base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex

variable {S : Scheme.{u}}



/-- The relative dualizing complex of a Cohen–Macaulay family of curves of
relative dimension 1 is bounded above by degree `-1`. -/
instance instIsLE_negOne {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) :
    C.complex.IsLE (-1) :=
  sorry

/-- The relative dualizing complex of a Cohen–Macaulay family of curves of
relative dimension 1 is bounded below by degree `-1`. -/
instance instIsGE_negOne {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) :
    C.complex.IsGE (-1) :=
  sorry

/-- Lemma 109.19.1 (1): the relative dualizing complex of a Cohen–Macaulay family
of curves of relative dimension 1 is the shift by `1` of its degree `-1`
cohomology sheaf. -/
@[stacks 0E6P]
theorem isIsomorphic_cohomologySheaf_shift {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) :
    IsIsomorphic C.complex
      (((DerivedCategory.singleFunctor (Modules X) 0).obj
          (cohomologySheaf C.complex (-1)))⟦(1 : ℤ)⟧) :=
  sorry

/-- The relative dualizing complex is recovered by placing its degree `-1`
cohomology sheaf in degree `-1`. -/
theorem isIsomorphic_single_negOne {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) :
    IsIsomorphic C.complex
      ((DerivedCategory.singleFunctor (Modules X) (-1)).obj
        (cohomologySheaf C.complex (-1))) :=
  sorry

/-- The shift form `ω[1]` is equivalent to placing the cohomology sheaf in
degree `-1`. -/
theorem isIsomorphic_cohomologySheaf_shift_iff     {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [CohenMacaulay f]
    [RelativeDimension f 1] (C : RelativeDualizingComplex f) :
    IsIsomorphic C.complex
        (((DerivedCategory.singleFunctor (Modules X) 0).obj
            (cohomologySheaf C.complex (-1)))⟦(1 : ℤ)⟧) ↔
      IsIsomorphic C.complex
        ((DerivedCategory.singleFunctor (Modules X) (-1)).obj
          (cohomologySheaf C.complex (-1))) :=
  sorry

/-- Lemma 109.19.1 (2): the degree `-1` cohomology sheaf of the relative
dualizing complex, viewed in degree `0`, is a pseudo-coherent derived
`𝒪_X`-module. -/
@[stacks 0E6P]
theorem cohomologySheaf_isPseudoCoherent {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) :
    IsPseudoCoherent X
      ((DerivedCategory.singleFunctor (Modules X) 0).obj
        (cohomologySheaf C.complex (-1))) :=
  sorry

/-- Lemma 109.19.1 (3): the degree `-1` cohomology sheaf of the relative
dualizing complex is flat over the base. -/
@[stacks 0E6P]
theorem cohomologySheaf_flatOver {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) :
    ∀ sq : EtaleSquare f,
      Scheme.Modules.IsStalkFlatOver
        ((Modules.restrictToScheme sq.left.left).obj
          ((Modules.pullback sq.left.hom).obj (cohomologySheaf C.complex (-1))))
        sq.map.left :=
  sorry

/-- Lemma 109.19.1 (4): formation of the degree `-1` cohomology sheaf of the
relative dualizing complex commutes with arbitrary base change. -/
@[stacks 0E6P]
theorem cohomologySheaf_baseChange {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] [IsFamily f] [CohenMacaulay f] [RelativeDimension f 1]
    (C : RelativeDualizingComplex f) {X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y')
    [∀ sq : EtaleSquare f',
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [∀ sq : EtaleSquare f',
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))] (g : Y' ⟶ Y)
    [IsFamily f'] [CohenMacaulay f'] [RelativeDimension f' 1]
    (sq : IsPullback g' f' f g) (C' : RelativeDualizingComplex f') :
    IsIsomorphic
      ((Modules.pullback g').obj (cohomologySheaf C.complex (-1)))
      (cohomologySheaf C'.complex (-1)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
