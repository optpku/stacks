/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Slice.Basic
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Transport

/-!
# Explicit-cleavage arbitrary-slice comparisons for cartesian Yoneda evaluation

This file compares arbitrary-slice evaluation with reindexing for a supplied cleavage. It owns
the fiber isomorphisms and their computation, naturality, and slice-restriction interfaces.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor
open Functor.Fiber

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace CartesianBasedFunctor.Yoneda.Slice.Explicit

/-- The ambient comparison between arbitrary-slice evaluation and reindexing for a supplied
cleavage. -/
@[stacks 0GWI "explicit-cleavage ambient arbitrary-slice comparison"]
noncomputable def evaluationIsoAmbient (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) (a : Over U) :
    ((F.fiberFunctor a.left).obj (fiberObj a)).1 ≅
      (a.hom⁎[chi]
        ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F)).1 :=
  Functor.Cleavage.SliceSection.Comparison.ambient
    (BasedCategory.ofFunctor p) chi F a

namespace evaluationIsoAmbient

/-- The forward ambient comparison is vertical over the identity of the slice domain. -/
theorem hom.isHomLift (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) (a : Over U) :
    p.IsHomLift (CategoryStruct.id a.left)
      (evaluationIsoAmbient p chi F a).hom := sorry

/-- The inverse ambient comparison is vertical over the identity of the slice domain. -/
theorem inv.isHomLift (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) (a : Over U) :
    p.IsHomLift (CategoryStruct.id a.left)
      (evaluationIsoAmbient p chi F a).inv := sorry

end evaluationIsoAmbient

/-- Evaluation at an arbitrary slice object is canonically isomorphic to reindexing, for a
supplied cleavage, of evaluation at the identity slice object. -/
@[stacks 0GWI "explicit-cleavage arbitrary-slice evaluation comparison"]
noncomputable def evaluationIso (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) (a : Over U) :
    (F.fiberFunctor a.left).obj (fiberObj a) ≅
      a.hom⁎[chi] ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F) :=
  Functor.Fiber.isoMk (evaluationIsoAmbient p chi F a)
    (hhom := evaluationIsoAmbient.hom.isHomLift p chi F a)

namespace evaluationIso

/-- The explicit-cleavage comparison is characterized by postcomposition with the supplied
cartesian arrow. -/
@[reassoc]
theorem hom.comp_cartesian (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) (a : Over U) :
    (evaluationIso p chi F a).hom.1 ≫
        chi.cartesianHom a.hom
          ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F) =
      evaluationHom p F a := sorry

/-- Expanded factorization of the explicit-cleavage comparison before codomain normalization. -/
theorem hom.comp_cartesian_transport (p : S ⥤ C) (chi : p.Cleavage)
    {U : C} (F : CartesianBasedFunctor.Yoneda.hom p U) (a : Over U) :
    (evaluationIso p chi F a).hom.1 ≫
        chi.cartesianHom a.hom
          ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F) ≫
        eqToHom (CartesianBasedFunctor.Yoneda.evaluation.obj p U F) =
      F.toFunctor.map (Over.mkIdTerminal.from a) := sorry

/-- The explicit-cleavage arbitrary-slice comparison is natural in the cartesian based
functor. -/
@[reassoc]
theorem hom.naturality (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    {F G : CartesianBasedFunctor.Yoneda.hom p U} (eta : F ⟶ G)
    (a : Over U) :
    BasedNatTrans.fiberApp eta.hom a.left (fiberObj a) ≫
        (evaluationIso p chi G a).hom =
      (evaluationIso p chi F a).hom ≫
        (a.hom⁎[chi]).map
          ((CartesianBasedFunctor.Yoneda.evaluation p U).map eta) := sorry

/-- Inverse form of naturality of the explicit-cleavage arbitrary-slice comparison. -/
@[reassoc]
theorem inv.naturality (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    {F G : CartesianBasedFunctor.Yoneda.hom p U} (eta : F ⟶ G)
    (a : Over U) :
    (evaluationIso p chi F a).inv ≫
        BasedNatTrans.fiberApp eta.hom a.left (fiberObj a) =
      (a.hom⁎[chi]).map
          ((CartesianBasedFunctor.Yoneda.evaluation p U).map eta) ≫
        (evaluationIso p chi G a).inv := sorry

/-- Restriction along a slice morphism agrees with iterated reindexing, including the canonical
base-composition transport. -/
theorem hom.restrict (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) {a b : Over U}
    (phi : a ⟶ b) :
    F.toFunctor.map phi ≫ (evaluationIso p chi F b).hom.1 =
      (evaluationIso p chi F a).hom.1 ≫
        (Functor.Cleavage.Reindex.specifiedCompIsoApp chi b.hom phi.left a.hom
          (Over.w phi)
          ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F)).hom.1 ≫
        chi.cartesianHom phi.left
          (b.hom⁎[chi]
            ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F)) := sorry

/-- Inverse restriction along a slice morphism agrees with iterated reindexing, including the
canonical base-composition transport. -/
theorem inv.restrict (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) {a b : Over U}
    (phi : a ⟶ b) :
    (evaluationIso p chi F a).inv.1 ≫ F.toFunctor.map phi =
      (Functor.Cleavage.Reindex.specifiedCompIsoApp chi b.hom phi.left a.hom
          (Over.w phi)
          ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F)).hom.1 ≫
        chi.cartesianHom phi.left
            (b.hom⁎[chi]
              ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F)) ≫
          (evaluationIso p chi F b).inv.1 := sorry

end evaluationIso

/-- Evaluation of the supplied-cleavage Yoneda section at an arbitrary slice object is
reindexing of the original fiber object. -/
@[stacks 0GWI "explicit-cleavage arbitrary-slice section comparison"]
noncomputable def sectionIso (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    (x : p.Fiber U) (a : Over U) :
    (((CartesianBasedFunctor.Yoneda.sectionOfCleavage p chi U).obj x).fiberFunctor
        a.left).obj (fiberObj a) ≅
      a.hom⁎[chi] x :=
  evaluationIso p chi
      ((CartesianBasedFunctor.Yoneda.sectionOfCleavage p chi U).obj x) a ≪≫
    (a.hom⁎[chi]).mapIso
      (CartesianBasedFunctor.Yoneda.counitIso.app p chi x)

namespace sectionIso

/-- The supplied-cleavage section comparison is characterized by the actual slice restriction
followed by the Yoneda counit. -/
@[reassoc]
theorem hom.comp_cartesian (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    (x : p.Fiber U) (a : Over U) :
    ((CartesianBasedFunctor.Yoneda.sectionOfCleavage p chi U).obj x).toFunctor.map
          (Over.mkIdTerminal.from a) ≫
        (CartesianBasedFunctor.Yoneda.counitIso.app p chi x).hom.1 =
      (sectionIso p chi x a).hom.1 ≫ chi.cartesianHom a.hom x := sorry

/-- The supplied-cleavage section comparison is natural in the original fiber object. -/
@[reassoc]
theorem hom.naturality (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    {x y : p.Fiber U} (f : x ⟶ y) (a : Over U) :
    BasedNatTrans.fiberApp
          ((CartesianBasedFunctor.Yoneda.sectionOfCleavage p chi U).map f).hom
          a.left (fiberObj a) ≫
        (sectionIso p chi y a).hom =
      (sectionIso p chi x a).hom ≫ (a.hom⁎[chi]).map f := sorry

/-- The inverse supplied-cleavage section comparison is natural in the original fiber object. -/
@[reassoc]
theorem inv.naturality (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    {x y : p.Fiber U} (f : x ⟶ y) (a : Over U) :
    (sectionIso p chi x a).inv ≫
        BasedNatTrans.fiberApp
          ((CartesianBasedFunctor.Yoneda.sectionOfCleavage p chi U).map f).hom
          a.left (fiberObj a) =
      (a.hom⁎[chi]).map f ≫ (sectionIso p chi y a).inv := sorry

/-- Restriction of the supplied-cleavage Yoneda section along a slice morphism agrees with
iterated reindexing. -/
theorem hom.restrict (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    (x : p.Fiber U) {a b : Over U} (phi : a ⟶ b) :
    ((CartesianBasedFunctor.Yoneda.sectionOfCleavage p chi U).obj x).toFunctor.map phi ≫
        (sectionIso p chi x b).hom.1 =
      (sectionIso p chi x a).hom.1 ≫
        (Functor.Cleavage.Reindex.specifiedCompIsoApp chi b.hom phi.left a.hom
          (Over.w phi) x).hom.1 ≫
        chi.cartesianHom phi.left (b.hom⁎[chi] x) := sorry

/-- Inverse restriction of the supplied-cleavage Yoneda section agrees with iterated
reindexing. -/
theorem inv.restrict (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    (x : p.Fiber U) {a b : Over U} (phi : a ⟶ b) :
    (sectionIso p chi x a).inv.1 ≫
        ((CartesianBasedFunctor.Yoneda.sectionOfCleavage p chi U).obj x).toFunctor.map phi =
      (Functor.Cleavage.Reindex.specifiedCompIsoApp chi b.hom phi.left a.hom
          (Over.w phi) x).hom.1 ≫
        chi.cartesianHom phi.left (b.hom⁎[chi] x) ≫
          (sectionIso p chi x b).inv.1 := sorry

end sectionIso

end CartesianBasedFunctor.Yoneda.Slice.Explicit

end CategoryTheory

/- Data audit: both fiber isomorphisms reuse the neutral slice-section comparison and the supplied
cleavage section; deferred axioms occur only in their proof and coherence fields. -/
