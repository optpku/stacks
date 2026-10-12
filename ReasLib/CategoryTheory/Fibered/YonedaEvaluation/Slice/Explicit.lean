/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Slice.Basic

/-!
# Explicit-cleavage arbitrary-slice comparisons for fibered Yoneda evaluation

This file adapts the neutral arbitrary-slice comparison to a bundled fibred category equipped
with a supplied cleavage. It exposes the ambient readout, computation rules, naturality in both
directions, and restriction along slice morphisms.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Functor
open Functor.Fiber
open FiberedCategoryOver
open CartesianBasedFunctor.Yoneda.Slice (fiberObj)

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.YonedaSlice.sectionOfCleavage

variable (X : FiberedCategoryOver C)

/-- The ambient isomorphism comparing evaluation at a slice object with reindexing for a supplied
cleavage. It is the canonical uniqueness isomorphism between two strongly cartesian arrows over
`a.hom`. -/
@[stacks 0GWI "explicit-cleavage ambient arbitrary-slice Yoneda comparison"]
noncomputable def evaluationIsoAmbient (χ : X.p.Cleavage) {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    ((fiberFunctor F a.left).obj (fiberObj a)).1 ≅
      (a.hom⁎[χ] ((evaluation X U).obj F)).1 :=
  CartesianBasedFunctor.Yoneda.Slice.Explicit.evaluationIsoAmbient X.p χ
    (FiberedCategoryOver.toCartesianBasedFunctor F) a

namespace evaluationIsoAmbient

/-- The forward explicit-cleavage ambient comparison is vertical over the identity of the slice
domain. -/
theorem hom.isHomLift (χ : X.p.Cleavage) {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    X.p.IsHomLift (𝟙 a.left) (evaluationIsoAmbient X χ F a).hom := sorry

/-- The inverse explicit-cleavage ambient comparison is vertical over the identity of the slice
domain. -/
theorem inv.isHomLift (χ : X.p.Cleavage) {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    X.p.IsHomLift (𝟙 a.left) (evaluationIsoAmbient X χ F a).inv := sorry

end evaluationIsoAmbient

/-- Evaluation at any slice object is canonically isomorphic to reindexing, for a supplied
cleavage, of evaluation at the identity slice object. -/
@[stacks 0GWI "explicit-cleavage arbitrary-slice Yoneda evaluation comparison"]
noncomputable def evaluationIso (χ : X.p.Cleavage) {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    (fiberFunctor F a.left).obj (fiberObj a) ≅
      a.hom⁎[χ] ((evaluation X U).obj F) :=
  CartesianBasedFunctor.Yoneda.Slice.Explicit.evaluationIso X.p χ
    (FiberedCategoryOver.toCartesianBasedFunctor F) a

namespace evaluationIso

/-- The underlying total-category arrow of the forward fiber comparison is the ambient forward
comparison. -/
@[simp]
theorem hom.val (χ : X.p.Cleavage) {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    (evaluationIso X χ F a).hom.1 = (evaluationIsoAmbient X χ F a).hom := sorry

/-- The underlying total-category arrow of the inverse fiber comparison is the ambient inverse
comparison. -/
@[simp]
theorem inv.val (χ : X.p.Cleavage) {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    (evaluationIso X χ F a).inv.1 = (evaluationIsoAmbient X χ F a).inv := sorry

/-- The explicit-cleavage slice-evaluation comparison is characterized by postcomposition with
the supplied cartesian arrow. -/
@[reassoc]
theorem hom.comp_cartesian (χ : X.p.Cleavage) {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    (evaluationIso X χ F a).hom.1 ≫
        χ.cartesianHom a.hom ((evaluation X U).obj F) =
      evaluationHom X F a := sorry

/-- Expanded factorization of the explicit-cleavage slice-evaluation comparison before codomain
normalization. -/
theorem hom.comp_cartesian_transport (χ : X.p.Cleavage) {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) (a : Over U) :
    (evaluationIso X χ F a).hom.1 ≫
        χ.cartesianHom a.hom ((evaluation X U).obj F) ≫
        eqToHom (evaluation.obj X U F) =
      (toFunctor F).map (Over.mkIdTerminal.from a) := sorry

/-- The explicit-cleavage arbitrary-slice evaluation comparison is natural in the fibred
morphism from the slice projection to `X`. -/
@[reassoc]
theorem hom.naturality (χ : X.p.Cleavage) {U : C}
    {F G : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X}
    (η : F ⟶ G) (a : Over U) :
    BasedNatTrans.fiberApp η.hom a.left (fiberObj a) ≫
        (evaluationIso X χ G a).hom =
      (evaluationIso X χ F a).hom ≫
        (a.hom⁎[χ]).map ((evaluation X U).map η) := sorry

/-- Inverse form of naturality of the explicit-cleavage arbitrary-slice evaluation comparison. -/
@[reassoc]
theorem inv.naturality (χ : X.p.Cleavage) {U : C}
    {F G : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X}
    (η : F ⟶ G) (a : Over U) :
    (evaluationIso X χ F a).inv ≫
        BasedNatTrans.fiberApp η.hom a.left (fiberObj a) =
      (a.hom⁎[χ]).map ((evaluation X U).map η) ≫
        (evaluationIso X χ G a).inv := sorry

/-- Restriction of explicit-cleavage slice evaluation along a slice morphism agrees with iterated
reindexing, including the canonical base-composition transport. -/
theorem hom.restrict (χ : X.p.Cleavage) {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X)
    {a b : Over U} (φ : a ⟶ b) :
    (toFunctor F).map φ ≫ (evaluationIso X χ F b).hom.1 =
      (evaluationIso X χ F a).hom.1 ≫
        (Functor.Cleavage.Reindex.specifiedCompIsoApp χ b.hom φ.left a.hom
          (Over.w φ) ((evaluation X U).obj F)).hom.1 ≫
        χ.cartesianHom φ.left (b.hom⁎[χ] ((evaluation X U).obj F)) := sorry

/-- Inverse restriction of explicit-cleavage slice evaluation agrees with iterated reindexing,
including the canonical base-composition transport. -/
theorem inv.restrict (χ : X.p.Cleavage) {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X)
    {a b : Over U} (φ : a ⟶ b) :
    (evaluationIso X χ F a).inv.1 ≫ (toFunctor F).map φ =
      (Functor.Cleavage.Reindex.specifiedCompIsoApp χ b.hom φ.left a.hom
          (Over.w φ) ((evaluation X U).obj F)).hom.1 ≫
        χ.cartesianHom φ.left (b.hom⁎[χ] ((evaluation X U).obj F)) ≫
          (evaluationIso X χ F b).inv.1 := sorry

end evaluationIso

/-- Evaluation of the explicit-cleavage Yoneda section at an arbitrary slice object is
reindexing, for that cleavage, of the original fiber object. -/
@[stacks 0GWI "explicit-cleavage arbitrary-slice Yoneda section comparison"]
noncomputable def sectionIso (χ : X.p.Cleavage) {U : C}
    (x : X.p.Fiber U) (a : Over U) :
    (fiberFunctor ((sectionOfCleavage X χ U).obj x) a.left).obj
        (fiberObj a) ≅ a.hom⁎[χ] x :=
  CartesianBasedFunctor.Yoneda.Slice.Explicit.sectionIso X.p χ x a

namespace sectionIso

/-- The arbitrary-slice comparison for the explicit-cleavage Yoneda section is characterized by
the actual slice restriction followed by the explicit-cleavage Yoneda counit. -/
@[reassoc]
theorem hom.comp_cartesian (χ : X.p.Cleavage) {U : C}
    (x : X.p.Fiber U) (a : Over U) :
    (toFunctor ((sectionOfCleavage X χ U).obj x)).map
          (Over.mkIdTerminal.from a) ≫
        (sectionOfCleavage.counitIso.app X χ x).hom.1 =
      (sectionIso X χ x a).hom.1 ≫ χ.cartesianHom a.hom x := sorry

/-- The forward arbitrary-slice comparison for the explicit-cleavage Yoneda section is natural
in the original fiber object. -/
@[reassoc]
theorem hom.naturality (χ : X.p.Cleavage) {U : C}
    {x y : X.p.Fiber U} (φ : x ⟶ y) (a : Over U) :
    BasedNatTrans.fiberApp ((sectionOfCleavage X χ U).map φ).hom a.left
          (fiberObj a) ≫
        (sectionIso X χ y a).hom =
      (sectionIso X χ x a).hom ≫ (a.hom⁎[χ]).map φ := sorry

/-- The inverse arbitrary-slice comparison for the explicit-cleavage Yoneda section is natural
in the original fiber object. -/
@[reassoc]
theorem inv.naturality (χ : X.p.Cleavage) {U : C}
    {x y : X.p.Fiber U} (φ : x ⟶ y) (a : Over U) :
    (sectionIso X χ x a).inv ≫
        BasedNatTrans.fiberApp ((sectionOfCleavage X χ U).map φ).hom a.left
          (fiberObj a) =
      (a.hom⁎[χ]).map φ ≫ (sectionIso X χ y a).inv := sorry

/-- Restriction of the explicit-cleavage Yoneda section along a slice morphism agrees with the
corresponding iterated reindexing, including the canonical base-composition transport. -/
theorem hom.restrict (χ : X.p.Cleavage) {U : C}
    (x : X.p.Fiber U) {a b : Over U} (φ : a ⟶ b) :
    (toFunctor ((sectionOfCleavage X χ U).obj x)).map φ ≫
        (sectionIso X χ x b).hom.1 =
      (sectionIso X χ x a).hom.1 ≫
        (Functor.Cleavage.Reindex.specifiedCompIsoApp χ b.hom φ.left a.hom
          (Over.w φ) x).hom.1 ≫
        χ.cartesianHom φ.left (b.hom⁎[χ] x) := sorry

/-- Inverse restriction of the explicit-cleavage Yoneda section agrees with iterated
reindexing, including the canonical base-composition transport. -/
theorem inv.restrict (χ : X.p.Cleavage) {U : C}
    (x : X.p.Fiber U) {a b : Over U} (φ : a ⟶ b) :
    (sectionIso X χ x a).inv.1 ≫
        (toFunctor ((sectionOfCleavage X χ U).obj x)).map φ =
      (Functor.Cleavage.Reindex.specifiedCompIsoApp χ b.hom φ.left a.hom
          (Over.w φ) x).hom.1 ≫
        χ.cartesianHom φ.left (b.hom⁎[χ] x) ≫
          (sectionIso X χ x b).inv.1 := sorry

end sectionIso

end FiberedCategoryOver.YonedaSlice.sectionOfCleavage

end CategoryTheory

/- Data audit: both comparison isomorphisms delegate their non-Prop payload to the neutral
cartesian based functor owner. Deferred axioms occur only in verticality, computation, naturality,
and coherence statements. -/
