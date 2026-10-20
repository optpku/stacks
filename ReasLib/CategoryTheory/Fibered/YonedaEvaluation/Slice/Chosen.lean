module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Slice.Explicit

/-!
# Selected-cleavage arbitrary-slice comparisons for fibered Yoneda evaluation

This file specializes the explicit-cleavage comparison API to the cleavage selected directly
from a bundled fibredness witness.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Functor
open Functor.Fiber
open FiberedCategoryOver
open CartesianBasedFunctor.Yoneda.Slice (fiberObj)

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.YonedaSlice

variable (X : FiberedCategoryOver C)

/-- Evaluation at any slice object is canonically isomorphic to reindexing by the cleavage
selected directly from `X`. -/
@[stacks 0GWI "selected-cleavage arbitrary-slice Yoneda evaluation comparison"]
noncomputable def evaluationIso {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    (fiberFunctor F a.left).obj (fiberObj a) ≅
      (Functor.Chosen.reindex X.p a.hom).obj ((evaluation X U).obj F) :=
  sectionOfCleavage.evaluationIso X X.chosenCleavage F a

namespace evaluationIso

/-- The underlying total-category arrow of the selected forward fiber comparison is the ambient
forward comparison for the selected cleavage. -/
@[simp]
theorem hom.val {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    (evaluationIso X F a).hom.1 =
      (sectionOfCleavage.evaluationIsoAmbient X X.chosenCleavage F a).hom := sorry

/-- The underlying total-category arrow of the selected inverse fiber comparison is the ambient
inverse comparison for the selected cleavage. -/
@[simp]
theorem inv.val {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    (evaluationIso X F a).inv.1 =
      (sectionOfCleavage.evaluationIsoAmbient X X.chosenCleavage F a).inv := sorry

/-- The selected-cleavage slice-evaluation comparison is characterized by postcomposition with
the selected cartesian arrow. -/
@[reassoc]
theorem hom.comp_cartesian {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    (evaluationIso X F a).hom.1 ≫
        Functor.Chosen.cartesianHom X.p a.hom ((evaluation X U).obj F) =
      evaluationHom X F a := sorry

/-- Expanded factorization of the selected-cleavage slice-evaluation comparison before codomain
normalization. -/
theorem hom.comp_cartesian_transport {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    (evaluationIso X F a).hom.1 ≫
        Functor.Chosen.cartesianHom X.p a.hom ((evaluation X U).obj F) ≫
        eqToHom (evaluation.obj X U F) =
      (toFunctor F).map (Over.mkIdTerminal.from a) := sorry

/-- The selected-cleavage arbitrary-slice evaluation comparison is natural in the fibred
morphism from the slice projection to `X`. -/
@[reassoc]
theorem hom.naturality {U : C}
    {F G : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X}
    (η : F ⟶ G) (a : Over U) :
    BasedNatTrans.fiberApp η.hom a.left (fiberObj a) ≫
        (evaluationIso X G a).hom =
      (evaluationIso X F a).hom ≫
        (Functor.Chosen.reindex X.p a.hom).map
          ((evaluation X U).map η) := sorry

/-- Inverse form of naturality of the selected-cleavage arbitrary-slice evaluation comparison. -/
@[reassoc]
theorem inv.naturality {U : C}
    {F G : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X}
    (η : F ⟶ G) (a : Over U) :
    (evaluationIso X F a).inv ≫
        BasedNatTrans.fiberApp η.hom a.left (fiberObj a) =
      (Functor.Chosen.reindex X.p a.hom).map
          ((evaluation X U).map η) ≫
        (evaluationIso X G a).inv := sorry

/-- Restriction of selected-cleavage slice evaluation along a slice morphism agrees with iterated
selected reindexing, including the canonical base-composition transport. -/
theorem hom.restrict {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X)
    {a b : Over U} (φ : a ⟶ b) :
    (toFunctor F).map φ ≫ (evaluationIso X F b).hom.1 =
      (evaluationIso X F a).hom.1 ≫
        (Functor.Chosen.Reindex.specifiedCompIsoApp X.p b.hom φ.left a.hom
          (Over.w φ) ((evaluation X U).obj F)).hom.1 ≫
        Functor.Chosen.cartesianHom X.p φ.left
          ((Functor.Chosen.reindex X.p b.hom).obj
            ((evaluation X U).obj F)) := sorry

/-- Inverse restriction of selected-cleavage slice evaluation agrees with iterated selected
reindexing, including the canonical base-composition transport. -/
theorem inv.restrict {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X)
    {a b : Over U} (φ : a ⟶ b) :
    (evaluationIso X F a).inv.1 ≫ (toFunctor F).map φ =
      (Functor.Chosen.Reindex.specifiedCompIsoApp X.p b.hom φ.left a.hom
          (Over.w φ) ((evaluation X U).obj F)).hom.1 ≫
        Functor.Chosen.cartesianHom X.p φ.left
            ((Functor.Chosen.reindex X.p b.hom).obj
              ((evaluation X U).obj F)) ≫
          (evaluationIso X F b).inv.1 := sorry

end evaluationIso

namespace QuasiInverse

/-- Evaluation of the selected Yoneda section at an arbitrary slice object is selected
reindexing of the original fiber object. -/
@[stacks 0GWI "selected-cleavage arbitrary-slice Yoneda section comparison"]
noncomputable def sectionIso {U : C}
    (x : X.p.Fiber U) (a : Over U) :
    (fiberFunctor ((functor X U).obj x) a.left).obj (fiberObj a) ≅
      (Functor.Chosen.reindex X.p a.hom).obj x :=
  sectionOfCleavage.sectionIso X X.chosenCleavage x a

namespace sectionIso

/-- The selected arbitrary-slice Yoneda section comparison is characterized by the actual slice
restriction followed by the selected-cleavage Yoneda counit. -/
@[reassoc]
theorem hom.comp_cartesian {U : C}
    (x : X.p.Fiber U) (a : Over U) :
    (toFunctor ((functor X U).obj x)).map (Over.mkIdTerminal.from a) ≫
        (counitIso.app X x).hom.1 =
      (sectionIso X x a).hom.1 ≫
        Functor.Chosen.cartesianHom X.p a.hom x := sorry

/-- The forward selected arbitrary-slice Yoneda section comparison is natural in the original
fiber object. -/
@[reassoc]
theorem hom.naturality {U : C}
    {x y : X.p.Fiber U} (φ : x ⟶ y) (a : Over U) :
    BasedNatTrans.fiberApp ((functor X U).map φ).hom a.left (fiberObj a) ≫
        (sectionIso X y a).hom =
      (sectionIso X x a).hom ≫
        (Functor.Chosen.reindex X.p a.hom).map φ := sorry

/-- The inverse selected arbitrary-slice Yoneda section comparison is natural in the original
fiber object. -/
@[reassoc]
theorem inv.naturality {U : C}
    {x y : X.p.Fiber U} (φ : x ⟶ y) (a : Over U) :
    (sectionIso X x a).inv ≫
        BasedNatTrans.fiberApp ((functor X U).map φ).hom a.left (fiberObj a) =
      (Functor.Chosen.reindex X.p a.hom).map φ ≫
        (sectionIso X y a).inv := sorry

/-- Restriction of the selected Yoneda section along a slice morphism agrees with the
corresponding iterated selected reindexing, including the canonical base-composition transport. -/
theorem hom.restrict {U : C}
    (x : X.p.Fiber U) {a b : Over U} (φ : a ⟶ b) :
    (toFunctor ((functor X U).obj x)).map φ ≫ (sectionIso X x b).hom.1 =
      (sectionIso X x a).hom.1 ≫
        (Functor.Chosen.Reindex.specifiedCompIsoApp X.p b.hom φ.left a.hom
          (Over.w φ) x).hom.1 ≫
        Functor.Chosen.cartesianHom X.p φ.left
          ((Functor.Chosen.reindex X.p b.hom).obj x) := sorry

/-- Inverse restriction of the selected Yoneda section agrees with iterated selected reindexing,
including the canonical base-composition transport. -/
theorem inv.restrict {U : C}
    (x : X.p.Fiber U) {a b : Over U} (φ : a ⟶ b) :
    (sectionIso X x a).inv.1 ≫ (toFunctor ((functor X U).obj x)).map φ =
      (Functor.Chosen.Reindex.specifiedCompIsoApp X.p b.hom φ.left a.hom
          (Over.w φ) x).hom.1 ≫
        Functor.Chosen.cartesianHom X.p φ.left
            ((Functor.Chosen.reindex X.p b.hom).obj x) ≫
          (sectionIso X x b).inv.1 := sorry

end sectionIso

end QuasiInverse

end FiberedCategoryOver.YonedaSlice

end CategoryTheory

/- Data audit: the selected comparison isomorphisms specialize the explicit-cleavage adapters to
`X.chosenCleavage`; deferred axioms occur only in computation, naturality, and coherence
statements. -/
