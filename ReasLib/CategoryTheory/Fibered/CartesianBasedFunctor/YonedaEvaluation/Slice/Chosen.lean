/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Slice.Explicit
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic

/-!
# Selected-cleavage arbitrary-slice comparisons for cartesian Yoneda evaluation

This file specializes the supplied-cleavage arbitrary-slice API to the cleavage selected by a
fibredness instance. It introduces no independent comparison data.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor
open Functor.Fiber

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace CartesianBasedFunctor.Yoneda.Slice.Chosen

variable (p : S ⥤ C) [p.IsFibered]

/-- Evaluation at an arbitrary slice object compared with the reindexing selected by a
fibredness instance. -/
@[stacks 0GWI "chosen arbitrary-slice evaluation comparison"]
noncomputable def evaluationIso {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) (a : Over U) :
    (F.fiberFunctor a.left).obj (fiberObj a) ≅
      (Functor.Chosen.reindex p a.hom).obj
        ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F) :=
  Explicit.evaluationIso p (Functor.Cleavage.ofIsFibered p) F a

namespace evaluationIso

/-- The chosen arbitrary-slice comparison is characterized by postcomposition with the selected
cartesian arrow. -/
@[reassoc]
theorem hom.comp_cartesian {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) (a : Over U) :
    (evaluationIso p F a).hom.1 ≫
        Functor.Chosen.cartesianHom p a.hom
          ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F) =
      evaluationHom p F a := sorry

/-- Expanded factorization of the chosen comparison before codomain normalization. -/
theorem hom.comp_cartesian_transport {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) (a : Over U) :
    (evaluationIso p F a).hom.1 ≫
        Functor.Chosen.cartesianHom p a.hom
          ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F) ≫
        eqToHom (CartesianBasedFunctor.Yoneda.evaluation.obj p U F) =
      F.toFunctor.map (Over.mkIdTerminal.from a) := sorry

/-- The chosen arbitrary-slice comparison is natural in the cartesian based functor. -/
@[reassoc]
theorem hom.naturality {U : C}
    {F G : CartesianBasedFunctor.Yoneda.hom p U} (eta : F ⟶ G)
    (a : Over U) :
    BasedNatTrans.fiberApp eta.hom a.left (fiberObj a) ≫
        (evaluationIso p G a).hom =
      (evaluationIso p F a).hom ≫
        (Functor.Chosen.reindex p a.hom).map
          ((CartesianBasedFunctor.Yoneda.evaluation p U).map eta) := sorry

/-- Inverse form of naturality of the chosen arbitrary-slice comparison. -/
@[reassoc]
theorem inv.naturality {U : C}
    {F G : CartesianBasedFunctor.Yoneda.hom p U} (eta : F ⟶ G)
    (a : Over U) :
    (evaluationIso p F a).inv ≫
        BasedNatTrans.fiberApp eta.hom a.left (fiberObj a) =
      (Functor.Chosen.reindex p a.hom).map
          ((CartesianBasedFunctor.Yoneda.evaluation p U).map eta) ≫
        (evaluationIso p G a).inv := sorry

/-- Restriction of chosen arbitrary-slice evaluation agrees with iterated selected reindexing. -/
theorem hom.restrict {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) {a b : Over U}
    (phi : a ⟶ b) :
    F.toFunctor.map phi ≫ (evaluationIso p F b).hom.1 =
      (evaluationIso p F a).hom.1 ≫
        (Functor.Chosen.Reindex.specifiedCompIsoApp p b.hom phi.left a.hom
          (Over.w phi)
          ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F)).hom.1 ≫
        Functor.Chosen.cartesianHom p phi.left
          ((Functor.Chosen.reindex p b.hom).obj
            ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F)) := sorry

/-- Inverse restriction of chosen arbitrary-slice evaluation agrees with iterated selected
reindexing. -/
theorem inv.restrict {U : C}
    (F : CartesianBasedFunctor.Yoneda.hom p U) {a b : Over U}
    (phi : a ⟶ b) :
    (evaluationIso p F a).inv.1 ≫ F.toFunctor.map phi =
      (Functor.Chosen.Reindex.specifiedCompIsoApp p b.hom phi.left a.hom
          (Over.w phi)
          ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F)).hom.1 ≫
        Functor.Chosen.cartesianHom p phi.left
            ((Functor.Chosen.reindex p b.hom).obj
              ((CartesianBasedFunctor.Yoneda.evaluation p U).obj F)) ≫
          (evaluationIso p F b).inv.1 := sorry

end evaluationIso

/-- Evaluation of the chosen Yoneda section at an arbitrary slice object is selected reindexing
of the original fiber object. -/
@[stacks 0GWI "chosen arbitrary-slice section comparison"]
noncomputable def sectionIso {U : C} (x : p.Fiber U) (a : Over U) :
    (((CartesianBasedFunctor.Yoneda.Chosen.functor p U).obj x).fiberFunctor
        a.left).obj (fiberObj a) ≅
      (Functor.Chosen.reindex p a.hom).obj x :=
  Explicit.sectionIso p (Functor.Cleavage.ofIsFibered p) x a

namespace sectionIso

/-- The chosen section comparison is characterized by the actual slice restriction followed by
the chosen Yoneda counit. -/
@[reassoc]
theorem hom.comp_cartesian {U : C} (x : p.Fiber U) (a : Over U) :
    ((CartesianBasedFunctor.Yoneda.Chosen.functor p U).obj x).toFunctor.map
          (Over.mkIdTerminal.from a) ≫
        (CartesianBasedFunctor.Yoneda.counitIso.app p
          (Functor.Cleavage.ofIsFibered p) x).hom.1 =
      (sectionIso p x a).hom.1 ≫
        Functor.Chosen.cartesianHom p a.hom x := sorry

/-- The chosen section comparison is natural in the original fiber object. -/
@[reassoc]
theorem hom.naturality {U : C} {x y : p.Fiber U} (f : x ⟶ y) (a : Over U) :
    BasedNatTrans.fiberApp
          ((CartesianBasedFunctor.Yoneda.Chosen.functor p U).map f).hom
          a.left (fiberObj a) ≫
        (sectionIso p y a).hom =
      (sectionIso p x a).hom ≫
        (Functor.Chosen.reindex p a.hom).map f := sorry

/-- The inverse chosen section comparison is natural in the original fiber object. -/
@[reassoc]
theorem inv.naturality {U : C} {x y : p.Fiber U} (f : x ⟶ y) (a : Over U) :
    (sectionIso p x a).inv ≫
        BasedNatTrans.fiberApp
          ((CartesianBasedFunctor.Yoneda.Chosen.functor p U).map f).hom
          a.left (fiberObj a) =
      (Functor.Chosen.reindex p a.hom).map f ≫
        (sectionIso p y a).inv := sorry

/-- Restriction of the chosen Yoneda section along a slice morphism agrees with iterated selected
reindexing. -/
theorem hom.restrict {U : C} (x : p.Fiber U) {a b : Over U} (phi : a ⟶ b) :
    ((CartesianBasedFunctor.Yoneda.Chosen.functor p U).obj x).toFunctor.map phi ≫
        (sectionIso p x b).hom.1 =
      (sectionIso p x a).hom.1 ≫
        (Functor.Chosen.Reindex.specifiedCompIsoApp p b.hom phi.left a.hom
          (Over.w phi) x).hom.1 ≫
        Functor.Chosen.cartesianHom p phi.left
          ((Functor.Chosen.reindex p b.hom).obj x) := sorry

/-- Inverse restriction of the chosen Yoneda section agrees with iterated selected reindexing. -/
theorem inv.restrict {U : C} (x : p.Fiber U) {a b : Over U} (phi : a ⟶ b) :
    (sectionIso p x a).inv.1 ≫
        ((CartesianBasedFunctor.Yoneda.Chosen.functor p U).obj x).toFunctor.map phi =
      (Functor.Chosen.Reindex.specifiedCompIsoApp p b.hom phi.left a.hom
          (Over.w phi) x).hom.1 ≫
        Functor.Chosen.cartesianHom p phi.left
            ((Functor.Chosen.reindex p b.hom).obj x) ≫
          (sectionIso p x b).inv.1 := sorry

end sectionIso

end CartesianBasedFunctor.Yoneda.Slice.Chosen

end CategoryTheory

/- Data audit: the selected-cleavage isomorphisms are direct specializations of the explicit
owners; any deferred axioms are inherited from proof and coherence fields. -/
