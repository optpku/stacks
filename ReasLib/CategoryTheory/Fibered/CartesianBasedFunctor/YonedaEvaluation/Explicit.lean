module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Basic
public import ReasLib.CategoryTheory.Fibered.Cleavage.SliceSection.Comparison
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Identity
public import ReasLib.CategoryTheory.Functor.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit-cleavage cartesian Yoneda equivalence

An explicit cleavage supplies the inverse section functor and the unit, counit, quasi-inverse,
and equivalence data for universe-polymorphic cartesian Yoneda evaluation.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor
open Functor.Fiber

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace CartesianBasedFunctor.Yoneda

/-- The inverse-direction cartesian slice-section functor determined by an explicit cleavage. Its
object and arrow data are the selected reindexing operations of the supplied cleavage. -/
@[stacks 0GWI "explicit-cleavage cartesian Yoneda section"]
noncomputable def sectionOfCleavage (p : S ⥤ C) (chi : p.Cleavage) (U : C) :
    p.Fiber U ⥤ hom p U :=
  Functor.Cleavage.SliceSection.functor (BasedCategory.ofFunctor p) chi U

namespace sectionOfCleavage

/-- The explicit-cleavage Yoneda section sends a fiber object to its cartesian cleavage section. -/
@[simp, stacks 0GWI "cartesian Yoneda section object readout"]
theorem obj (p : S ⥤ C) (chi : p.Cleavage) (U : C) (x : p.Fiber U) :
    (sectionOfCleavage p chi U).obj x =
      Functor.Cleavage.SliceSection.cartesian (BasedCategory.ofFunctor p) chi U x := sorry

/-- The explicit-cleavage Yoneda section sends a fiber morphism to the vertical transformation
whose components are its selected reindexings. -/
@[stacks 0GWI "cartesian Yoneda section morphism readout"]
theorem map.hom (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    {x y : p.Fiber U} (f : x ⟶ y) :
    ((sectionOfCleavage p chi U).map f).hom =
      Functor.Cleavage.SliceSection.natTrans (BasedCategory.ofFunctor p) chi f := sorry

end sectionOfCleavage

/-- A cartesian slice functor is canonically isomorphic to the explicit-cleavage section of its
value at the identity slice object. -/
@[stacks 0GWI "explicit-cleavage cartesian Yoneda unit component"]
noncomputable def unitIso.app (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    (F : hom p U) :
    F ≅ (sectionOfCleavage p chi U).obj ((evaluation p U).obj F) :=
  Functor.Cleavage.SliceSection.Comparison.iso (BasedCategory.ofFunctor p) chi F

/-- Evaluating an explicit-cleavage section at the identity slice object canonically recovers the
original fiber object. -/
@[stacks 0GWI "explicit-cleavage cartesian Yoneda counit component"]
noncomputable def counitIso.app (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    (x : p.Fiber U) :
    (evaluation p U).obj ((sectionOfCleavage p chi U).obj x) ≅ x :=
  (Functor.Cleavage.Reindex.idIsoApp chi U x).symm

namespace unitIso

/-- Naturality of the forward explicit-cleavage cartesian Yoneda unit. -/
@[reassoc]
theorem hom.naturality (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    {F G : hom p U} (eta : F ⟶ G) :
    eta ≫ (unitIso.app p chi G).hom =
      (unitIso.app p chi F).hom ≫
        (sectionOfCleavage p chi U).map ((evaluation p U).map eta) := sorry

/-- Naturality of the inverse explicit-cleavage cartesian Yoneda unit. -/
@[reassoc]
theorem inv.naturality (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    {F G : hom p U} (eta : F ⟶ G) :
    (sectionOfCleavage p chi U).map ((evaluation p U).map eta) ≫
        (unitIso.app p chi G).inv =
      (unitIso.app p chi F).inv ≫ eta := sorry

end unitIso

namespace counitIso

/-- Naturality of the forward explicit-cleavage cartesian Yoneda counit. -/
@[reassoc]
theorem hom.naturality (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    {x y : p.Fiber U} (f : x ⟶ y) :
    (evaluation p U).map ((sectionOfCleavage p chi U).map f) ≫
        (counitIso.app p chi y).hom =
      (counitIso.app p chi x).hom ≫ f := sorry

/-- Naturality of the inverse explicit-cleavage cartesian Yoneda counit. -/
@[reassoc]
theorem inv.naturality (p : S ⥤ C) (chi : p.Cleavage) {U : C}
    {x y : p.Fiber U} (f : x ⟶ y) :
    f ≫ (counitIso.app p chi y).inv =
      (counitIso.app p chi x).inv ≫
        (evaluation p U).map ((sectionOfCleavage p chi U).map f) := sorry

end counitIso

/-- The explicit-cleavage cartesian Yoneda unit components assembled into a natural isomorphism. -/
@[stacks 0GWI "explicit-cleavage cartesian Yoneda unit"]
noncomputable def unitIso (p : S ⥤ C) (chi : p.Cleavage) (U : C) :
    𝟭 (hom p U) ≅ evaluation p U ⋙ sectionOfCleavage p chi U :=
  NatIso.ofComponents (unitIso.app p chi)
    (fun eta ↦ unitIso.hom.naturality p chi eta)

/-- The explicit-cleavage cartesian Yoneda counit components assembled into a natural
isomorphism. -/
@[stacks 0GWI "explicit-cleavage cartesian Yoneda counit"]
noncomputable def counitIso (p : S ⥤ C) (chi : p.Cleavage) (U : C) :
    sectionOfCleavage p chi U ⋙ evaluation p U ≅ 𝟭 (p.Fiber U) :=
  NatIso.ofComponents (counitIso.app p chi)
    (fun f ↦ counitIso.hom.naturality p chi f)

/-- A component of the packaged explicit-cleavage cartesian Yoneda unit is its named objectwise
comparison. -/
@[simp, stacks 0GWI "cartesian Yoneda unit readout"]
theorem unitIso.hom.app (p : S ⥤ C) (chi : p.Cleavage) (U : C) (F : hom p U) :
    (unitIso p chi U).hom.app F = (unitIso.app p chi F).hom := sorry

/-- An inverse component of the packaged explicit-cleavage cartesian Yoneda unit is its named
objectwise comparison. -/
@[simp, stacks 0GWI "cartesian Yoneda inverse unit readout"]
theorem unitIso.inv.app (p : S ⥤ C) (chi : p.Cleavage) (U : C) (F : hom p U) :
    (unitIso p chi U).inv.app F = (unitIso.app p chi F).inv := sorry

/-- A component of the packaged explicit-cleavage cartesian Yoneda counit is its named objectwise
comparison. -/
@[simp, stacks 0GWI "cartesian Yoneda counit readout"]
theorem counitIso.hom.app (p : S ⥤ C) (chi : p.Cleavage) (U : C) (x : p.Fiber U) :
    (counitIso p chi U).hom.app x = (counitIso.app p chi x).hom := sorry

/-- An inverse component of the packaged explicit-cleavage cartesian Yoneda counit is its named
objectwise comparison. -/
@[simp, stacks 0GWI "cartesian Yoneda inverse counit readout"]
theorem counitIso.inv.app (p : S ⥤ C) (chi : p.Cleavage) (U : C) (x : p.Fiber U) :
    (counitIso p chi U).inv.app x = (counitIso.app p chi x).inv := sorry

/-- Explicit quasi-inverse data for universe-polymorphic cartesian Yoneda evaluation, retaining
the supplied cleavage section and its canonical unit and counit. -/
@[stacks 0GWI "explicit-cleavage cartesian Yoneda quasi-inverse"]
noncomputable def quasiInverse (p : S ⥤ C) (chi : p.Cleavage) (U : C) :
    Functor.QuasiInverse (evaluation p U) where
  inverse := sectionOfCleavage p chi U
  unitIso := unitIso p chi U
  counitIso := counitIso p chi U

namespace quasiInverse

/-- The inverse functor stored by the explicit cartesian Yoneda quasi-inverse is the supplied
cleavage section. -/
@[simp, stacks 0GWI "cartesian Yoneda quasi-inverse readout"]
theorem inverse (p : S ⥤ C) (chi : p.Cleavage) (U : C) :
    (quasiInverse p chi U).inverse = sectionOfCleavage p chi U := sorry

/-- The unit stored by the explicit cartesian Yoneda quasi-inverse is the named unit. -/
@[simp]
theorem unitIso (p : S ⥤ C) (chi : p.Cleavage) (U : C) :
    (quasiInverse p chi U).unitIso = CartesianBasedFunctor.Yoneda.unitIso p chi U := sorry

/-- The counit stored by the explicit cartesian Yoneda quasi-inverse is the named counit. -/
@[simp]
theorem counitIso (p : S ⥤ C) (chi : p.Cleavage) (U : C) :
    (quasiInverse p chi U).counitIso = CartesianBasedFunctor.Yoneda.counitIso p chi U := sorry

end quasiInverse

/-- The universe-polymorphic cartesian Yoneda equivalence determined by an explicit cleavage. -/
@[stacks 0GWI "explicit-cleavage cartesian Yoneda equivalence"]
noncomputable def equivalence (p : S ⥤ C) (chi : p.Cleavage) (U : C) :
    hom p U ≌ p.Fiber U :=
  (quasiInverse p chi U).adjointifyUnit

namespace equivalence

/-- The forward functor of the explicit cartesian Yoneda equivalence is evaluation. -/
@[simp]
theorem functor (p : S ⥤ C) (chi : p.Cleavage) (U : C) :
    (equivalence p chi U).functor = evaluation p U := sorry

/-- The inverse functor of the explicit cartesian Yoneda equivalence is the supplied cleavage
section. -/
@[simp, stacks 0GWI "cartesian Yoneda equivalence inverse readout"]
theorem inverse (p : S ⥤ C) (chi : p.Cleavage) (U : C) :
    (equivalence p chi U).inverse = sectionOfCleavage p chi U := sorry

/-- The counit retained by the explicit cartesian Yoneda equivalence is the named counit. -/
@[simp]
theorem counitIso (p : S ⥤ C) (chi : p.Cleavage) (U : C) :
    (equivalence p chi U).counitIso = CartesianBasedFunctor.Yoneda.counitIso p chi U := sorry

end equivalence

end CartesianBasedFunctor.Yoneda

end CategoryTheory
