/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Equivalence
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Explicit
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Basic.Evaluation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit-cleavage fixed-owner Yoneda equivalence

This leaf transports the neutral cleavage section and its comparison data to the fixed-owner
hom-category. The section, components, naturality, quasi-inverse, and equivalence remain explicit.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Functor
open Functor.Fiber
open FiberedCategoryOver

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.YonedaSlice

variable (X : FiberedCategoryOver C)

/-- The inverse-direction slice-section functor associated to an explicit cleavage. Its object and
arrow actions are inherited from the neutral cartesian cleavage section. -/
@[stacks 0GWI "explicit-cleavage Yoneda section"]
noncomputable def sectionOfCleavage (chi : X.p.Cleavage) (U : C) :
    X.p.Fiber U ⥤ (FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) :=
  CartesianBasedFunctor.Yoneda.sectionOfCleavage X.p chi U ⋙
    FiberedCategoryOver.CartesianHom.toHom
      (FiberedCategoryOver.ofFunctor (Over.forget U)) X

namespace sectionOfCleavage

/-- The fixed-owner section object is the fixed-owner image of the neutral cartesian section
object. -/
@[simp, stacks 0GWI "fixed-owner Yoneda section object readout"]
theorem obj (chi : X.p.Cleavage) (U : C) (x : X.p.Fiber U) :
    (sectionOfCleavage X chi U).obj x =
      (FiberedCategoryOver.CartesianHom.toHom
        (FiberedCategoryOver.ofFunctor (Over.forget U)) X).obj
          ((CartesianBasedFunctor.Yoneda.sectionOfCleavage X.p chi U).obj x) := sorry

/-- Forgetting a fixed-owner section object recovers the neutral cartesian section object. -/
@[simp]
theorem obj.toCartesianBasedFunctor (chi : X.p.Cleavage) (U : C) (x : X.p.Fiber U) :
    FiberedCategoryOver.toCartesianBasedFunctor ((sectionOfCleavage X chi U).obj x) =
      (CartesianBasedFunctor.Yoneda.sectionOfCleavage X.p chi U).obj x := sorry

/-- The underlying vertical transformation of the fixed-owner section map is the corresponding
neutral cartesian section map. -/
@[stacks 0GWI "fixed-owner Yoneda section morphism readout"]
theorem map.hom (chi : X.p.Cleavage) {U : C} {x y : X.p.Fiber U} (f : x ⟶ y) :
    ((sectionOfCleavage X chi U).map f).hom =
      ((CartesianBasedFunctor.Yoneda.sectionOfCleavage X.p chi U).map f).hom := sorry

/-- A morphism from the slice into `X` is canonically isomorphic to the section, for the
supplied cleavage, of its value at the identity slice object. -/
@[stacks 0GWI "explicit-cleavage Yoneda unit"]
noncomputable def unitIso.app (chi : X.p.Cleavage) {U : C}
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) :
    F ≅ (sectionOfCleavage X chi U).obj ((evaluation X U).obj F) :=
  FiberedCategoryOver.BasedFunctorIso.lift
    (Functor.Cleavage.SliceSection.Comparison.basedIso X.toBasedCategory chi
      (FiberedCategoryOver.toCartesianBasedFunctor F))

/-- Evaluating the Yoneda section for a supplied cleavage at the identity slice object recovers
the original fiber object. -/
@[stacks 0GWI "explicit-cleavage Yoneda counit"]
noncomputable def counitIso.app (chi : X.p.Cleavage) {U : C} (x : X.p.Fiber U) :
    (evaluation X U).obj ((sectionOfCleavage X chi U).obj x) ≅ x :=
  (Functor.Cleavage.Reindex.idIsoApp chi U x).symm

namespace unitIso

/-- Naturality of the forward explicit-cleavage Yoneda unit comparison. -/
@[reassoc]
theorem hom.naturality (chi : X.p.Cleavage) {U : C}
    {F G : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X} (eta : F ⟶ G) :
    eta ≫ (unitIso.app X chi G).hom =
      (unitIso.app X chi F).hom ≫
        (sectionOfCleavage X chi U).map ((evaluation X U).map eta) := sorry

/-- Naturality of the inverse explicit-cleavage Yoneda unit comparison. -/
@[reassoc]
theorem inv.naturality (chi : X.p.Cleavage) {U : C}
    {F G : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X} (eta : F ⟶ G) :
    (sectionOfCleavage X chi U).map ((evaluation X U).map eta) ≫
        (unitIso.app X chi G).inv = (unitIso.app X chi F).inv ≫ eta := sorry

end unitIso

namespace counitIso

/-- Naturality of the forward explicit-cleavage Yoneda counit comparison. -/
@[reassoc]
theorem hom.naturality (chi : X.p.Cleavage) {U : C}
    {x y : X.p.Fiber U} (f : x ⟶ y) :
    (evaluation X U).map ((sectionOfCleavage X chi U).map f) ≫
        (counitIso.app X chi y).hom = (counitIso.app X chi x).hom ≫ f := sorry

/-- Naturality of the inverse explicit-cleavage Yoneda counit comparison. -/
@[reassoc]
theorem inv.naturality (chi : X.p.Cleavage) {U : C}
    {x y : X.p.Fiber U} (f : x ⟶ y) :
    f ≫ (counitIso.app X chi y).inv =
      (counitIso.app X chi x).inv ≫
        (evaluation X U).map ((sectionOfCleavage X chi U).map f) := sorry

end counitIso

/-- The explicit-cleavage Yoneda unit components assembled into a natural isomorphism. -/
@[stacks 0GWI "explicit-cleavage Yoneda unit natural isomorphism"]
noncomputable def unitIso (chi : X.p.Cleavage) (U : C) :
    𝟭 (FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) ≅
      evaluation X U ⋙ sectionOfCleavage X chi U :=
  NatIso.ofComponents (unitIso.app X chi) (fun eta ↦ unitIso.hom.naturality X chi eta)

/-- The explicit-cleavage Yoneda counit components assembled into a natural isomorphism. -/
@[stacks 0GWI "explicit-cleavage Yoneda counit natural isomorphism"]
noncomputable def counitIso (chi : X.p.Cleavage) (U : C) :
    sectionOfCleavage X chi U ⋙ evaluation X U ≅ 𝟭 (X.p.Fiber U) :=
  NatIso.ofComponents (counitIso.app X chi) (fun f ↦ counitIso.hom.naturality X chi f)

/-- A component of the packaged explicit-cleavage Yoneda unit is its named comparison. -/
@[simp]
theorem unitIso.hom.app (chi : X.p.Cleavage) (U : C)
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) :
    (unitIso X chi U).hom.app F = (unitIso.app X chi F).hom := sorry

/-- An inverse component of the packaged explicit-cleavage Yoneda unit is its named comparison. -/
@[simp]
theorem unitIso.inv.app (chi : X.p.Cleavage) (U : C)
    (F : FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) :
    (unitIso X chi U).inv.app F = (unitIso.app X chi F).inv := sorry

/-- A component of the packaged explicit-cleavage Yoneda counit is its named comparison. -/
@[simp]
theorem counitIso.hom.app (chi : X.p.Cleavage) (U : C) (x : X.p.Fiber U) :
    (counitIso X chi U).hom.app x = (counitIso.app X chi x).hom := sorry

/-- An inverse component of the packaged explicit-cleavage Yoneda counit is its named comparison. -/
@[simp]
theorem counitIso.inv.app (chi : X.p.Cleavage) (U : C) (x : X.p.Fiber U) :
    (counitIso X chi U).inv.app x = (counitIso.app X chi x).inv := sorry

/-- A supplied cleavage section and its comparisons are explicit quasi-inverse data for
fixed-owner Yoneda evaluation. -/
@[stacks 0GWI "explicit-cleavage Yoneda quasi-inverse"]
noncomputable def quasiInverse (chi : X.p.Cleavage) (U : C) :
    Functor.QuasiInverse (evaluation X U) where
  inverse := sectionOfCleavage X chi U
  unitIso := unitIso X chi U
  counitIso := counitIso X chi U

namespace quasiInverse

/-- The inverse stored by the explicit quasi-inverse is the supplied cleavage section. -/
@[simp]
theorem inverse (chi : X.p.Cleavage) (U : C) :
    (quasiInverse X chi U).inverse = sectionOfCleavage X chi U := sorry

/-- The unit stored by the explicit quasi-inverse is the named unit. -/
@[simp]
theorem unitIso (chi : X.p.Cleavage) (U : C) :
    (quasiInverse X chi U).unitIso = sectionOfCleavage.unitIso X chi U := sorry

/-- The counit stored by the explicit quasi-inverse is the named counit. -/
@[simp]
theorem counitIso (chi : X.p.Cleavage) (U : C) :
    (quasiInverse X chi U).counitIso = sectionOfCleavage.counitIso X chi U := sorry

end quasiInverse

/-- The fixed-owner Yoneda equivalence whose inverse is the section for the supplied cleavage. -/
@[stacks 0GWI "explicit-cleavage Yoneda equivalence"]
noncomputable def equivalence (chi : X.p.Cleavage) (U : C) :
    (FiberedCategoryOver.ofFunctor (Over.forget U) ⟶ X) ≌ X.p.Fiber U :=
  (quasiInverse X chi U).adjointifyUnit

/-- The forward functor retained by the explicit equivalence is evaluation. -/
@[simp]
theorem equivalence.functor (chi : X.p.Cleavage) (U : C) :
    (equivalence X chi U).functor = evaluation X U := sorry

/-- The inverse retained by the explicit equivalence is the supplied cleavage section. -/
@[simp]
theorem equivalence.inverse (chi : X.p.Cleavage) (U : C) :
    (equivalence X chi U).inverse = sectionOfCleavage X chi U := sorry

/-- The counit retained by the explicit equivalence is the named counit. -/
@[simp]
theorem equivalence.counitIso (chi : X.p.Cleavage) (U : C) :
    (equivalence X chi U).counitIso = counitIso X chi U := sorry

end sectionOfCleavage

end FiberedCategoryOver.YonedaSlice

end CategoryTheory

/- Data audit: section and comparison data are inherited from the neutral cartesian owner and
the fixed-owner conversion; deferred axioms occur only in law, computation, and coherence fields. -/
