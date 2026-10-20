module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap99.Lemma_99_16_4
public import stacks_project.Chap110.Lemma_110_53_1

/-!
# Structure morphism of the stack of complexes

The forgetful 1-morphism `Complexes_{X/B} ⟶ B` in the Hom-universe of
`Classifying.toGroupoids`, sending a triple `(T, g, E)` to the functor-of-points
element of `g : T ⟶ B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The projection `(T, g, E) ↦ (T, g)` from the category of admissible complexes
on fibres of `f` to schemes over `B`. -/
def toSchemesOver (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f] :
    Obj f ⥤ SchemeOver B where
  obj x := x.σ
  map α := α.base
  map_id := sorry
  map_comp := sorry

/-- The object part of `toSchemesOver` is the test scheme of a complex. -/
theorem toSchemesOver_obj (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    (x : Obj f) :
    (toSchemesOver f).obj x = x.σ :=
  sorry

/-- The morphism part of `toSchemesOver` is the underlying map of schemes over
`B`. -/
theorem toSchemesOver_map {f : X ⟶ B}
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : Obj f} (α : x ⟶ y) :
    (toSchemesOver f).map α = α.base :=
  sorry

/-- Forgetting the structure map of a scheme over `B` recovers the projection to
`Over S`. -/
theorem toSchemesOver_comp_proj (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f]
    [FinitePresentation f] :
    toSchemesOver f ⋙ CostructuredArrow.proj (ofOverFunctor S) B = p f :=
  sorry

/-- The functor-of-points section of a morphism of algebraic spaces from a
scheme over `S`. -/
def functorOfPointsSection {T : Over S} (φ : ofOver T ⟶ B) :
    B.functorOfPoints.obj (op T) :=
  yonedaEquiv (φ : yoneda.obj T ⟶ B.functorOfPoints)

/-- `functorOfPointsSection φ` is the Yoneda evaluation of `φ`. -/
theorem functorOfPointsSection_eq {T : Over S} (φ : ofOver T ⟶ B) :
    functorOfPointsSection φ = yonedaEquiv (φ : yoneda.obj T ⟶ B.functorOfPoints) :=
  sorry

/-- The category-of-elements object classified by the structure map of a
complex. -/
def toBaseElement {f : X ⟶ B}
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    (x : Obj f) : B.functorOfPoints.Elements :=
  ⟨op x.σ.left, functorOfPointsSection x.σ.hom⟩

/-- The first component of `toBaseElement x` is the opposite of the test scheme
of `x`. -/
theorem toBaseElement_fst {f : X ⟶ B}
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    (x : Obj f) :
    (toBaseElement x).fst = op x.σ.left :=
  sorry

/-- The second component of `toBaseElement x` is the functor-of-points section of
the structure map of `x`. -/
theorem toBaseElement_snd {f : X ⟶ B}
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    (x : Obj f) :
    (toBaseElement x).snd = functorOfPointsSection x.σ.hom :=
  sorry

/-- Compatibility of functor-of-points sections with a morphism of complexes. -/
theorem toBaseHom_map_snd {f : X ⟶ B}
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : Obj f} (α : x ⟶ y) :
    B.functorOfPoints.map α.base.left.op (functorOfPointsSection y.σ.hom) =
      functorOfPointsSection x.σ.hom :=
  sorry

/-- The category-of-elements morphism induced by a morphism of complexes,
pointing from the target test scheme to the source so that its opposite lies
over `α.base.left`. -/
def toBaseHom {f : X ⟶ B}
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : Obj f} (α : x ⟶ y) :
    toBaseElement y ⟶ toBaseElement x :=
  CategoryOfElements.homMk (toBaseElement y) (toBaseElement x) α.base.left.op
    (toBaseHom_map_snd α)

/-- The underlying morphism of `toBaseHom α` is the opposite of the test-scheme
map of `α`. -/
theorem toBaseHom_val {f : X ⟶ B}
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : Obj f} (α : x ⟶ y) :
    (toBaseHom α).val = α.base.left.op :=
  sorry

/-- The total functor of the structure morphism `Complexes_{X/B} ⟶ B`, sending a
complex to the universe-lifted functor-of-points element of its structure
map. -/
def toBaseFunctor (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f] :
    Obj f ⥤ ULiftHom.{u + 1} B.functorOfPoints.Elementsᵒᵖ where
  obj x := ULiftHom.objUp (op (toBaseElement x))
  map α := ULiftHom.up.map (Quiver.Hom.op (toBaseHom α))
  map_id := sorry
  map_comp := sorry

/-- On objects, `toBaseFunctor` is `ULiftHom.objUp` of the opposite
category-of-elements object. -/
theorem toBaseFunctor_obj (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    (x : Obj f) :
    (toBaseFunctor f).obj x = ULiftHom.objUp (op (toBaseElement x)) :=
  sorry

/-- `toBaseFunctor` lies strictly over `(Sch/S)`. -/
theorem toBaseFunctor_p (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f] :
    toBaseFunctor f ⋙ Classifying.toGroupoidsProjection B = p f :=
  sorry

/-- The structure 1-morphism `Complexes_{X/B} ⟶ B` in the Hom-universe of
`Classifying.toGroupoids`, forgetting the complex and recording the test scheme
over `B`. -/
def toBase (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f] :
    toGroupoids f ⟶ Classifying.toGroupoids B :=
  ofBasedFunctor (BasedFunctor.ofFunctor (toBaseFunctor f) (toBaseFunctor_p f))

/-- The total functor of `toBase f` is `toBaseFunctor f`. -/
theorem toBase_toFunctor (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f] :
    toFunctor (toBase f) = toBaseFunctor f :=
  sorry

/-- `toBase f` lies strictly over `(Sch/S)`. -/
theorem toBase_p (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f] :
    toFunctor (toBase f) ⋙ (Classifying.toGroupoids B).p = p f :=
  sorry

/-- On a complex `x`, `toBase f` is the universe-lifted functor-of-points element
of the structure map of `x`. -/
theorem toBase_obj (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    (x : Obj f) :
    (toFunctor (toBase f)).obj x = ULiftHom.objUp (op (toBaseElement x)) :=
  sorry

/-- `toBase` forgets the complex and records the test scheme of
`toSchemesOver`. -/
theorem toBase_spec (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f]
    (x : Obj f) :
    (Classifying.toGroupoidsProjection B).obj ((toFunctor (toBase f)).obj x) =
      ((toSchemesOver f).obj x).left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
