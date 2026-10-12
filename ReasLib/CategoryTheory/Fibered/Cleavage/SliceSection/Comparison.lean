/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.SliceSection
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Yoneda.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Slice
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparing cartesian slice functors with cleavage sections

Every cartesian functor from `C/U` to a category over `C` is canonically isomorphic to the
slice section obtained by reindexing its value at `𝟙 U`.  This file owns that comparison at the
universe-polymorphic `CartesianBasedFunctor` layer, independently of bundled fibred categories
and of any property-selected quasi-inverse to evaluation.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace Functor.Cleavage.SliceSection.Comparison

/-- The ambient total-category comparison between a cartesian slice functor and the selected
reindexing of its value at the identity slice object. -/
@[stacks 0GWI "cartesian slice-section comparison"]
noncomputable def ambient
    (Y : BasedCategory.{vS, uS} C) (χ : Y.p.Cleavage) {U : C}
    (F : CartesianBasedFunctor (Over.forget U) Y.p) (a : Over U) :
    F.toFunctor.obj a ≅
      (χ.reindexObj a.hom
        ((BasedCategory.Yoneda.evaluation Y.p U).obj F.toBasedFunctor)).1 :=
  IsStronglyCartesian.DomainIso.ofBaseIso (g := Iso.refl a.left) Y.p
    (Category.id_comp a.hom).symm
    (χ.cartesianHom a.hom
      ((BasedCategory.Yoneda.evaluation Y.p U).obj F.toBasedFunctor))
    (F.toFunctor.map (Over.mkIdTerminal.from a))
    (cartesianHom.isStronglyCartesian χ a.hom
      ((BasedCategory.Yoneda.evaluation Y.p U).obj F.toBasedFunctor))
    (CartesianBasedFunctor.Map.stronglyCartesianOfLift F a.hom
      (Over.mkIdTerminal.from a) (Over.mkIdTerminal.from.isStronglyCartesian a))

/-- The forward ambient comparison is vertical over the identity of the slice source. -/
theorem ambient_hom_isHomLift
    (Y : BasedCategory.{vS, uS} C) (χ : Y.p.Cleavage) {U : C}
    (F : CartesianBasedFunctor (Over.forget U) Y.p) (a : Over U) :
    Y.p.IsHomLift (𝟙 a.left) (ambient Y χ F a).hom := sorry

/-- The ambient comparison is natural in the slice object. -/
theorem ambient_naturality
    (Y : BasedCategory.{vS, uS} C) (χ : Y.p.Cleavage) {U : C}
    (F : CartesianBasedFunctor (Over.forget U) Y.p)
    {a b : Over U} (f : a ⟶ b) :
    F.toFunctor.map f ≫ (ambient Y χ F b).hom =
      (ambient Y χ F a).hom ≫
        (based Y χ U
          ((BasedCategory.Yoneda.evaluation Y.p U).obj F.toBasedFunctor)).map f := sorry

/-- A cartesian slice functor is isomorphic, as a based functor, to the cleavage section of its
value at the identity slice object. -/
@[stacks 0GWI "based cartesian slice-section comparison"]
noncomputable def basedIso
    (Y : BasedCategory.{vS, uS} C) (χ : Y.p.Cleavage) {U : C}
    (F : CartesianBasedFunctor (Over.forget U) Y.p) :
    F.toBasedFunctor ≅
      based Y χ U
        ((BasedCategory.Yoneda.evaluation Y.p U).obj F.toBasedFunctor) :=
  BasedNatIso.ofComponents (ambient Y χ F)
    (ambient_naturality Y χ F) (ambient_hom_isHomLift Y χ F)

/-- A cartesian slice functor is isomorphic to the cartesian cleavage section of its value at
the identity slice object. -/
@[stacks 0GWI "cartesian slice-section isomorphism"]
noncomputable def iso
    (Y : BasedCategory.{vS, uS} C) (χ : Y.p.Cleavage) {U : C}
    (F : CartesianBasedFunctor (Over.forget U) Y.p) :
    F ≅ cartesian Y χ U
      ((BasedCategory.Yoneda.evaluation Y.p U).obj F.toBasedFunctor) :=
  ObjectProperty.isoMk _ (basedIso Y χ F)

end Functor.Cleavage.SliceSection.Comparison

end CategoryTheory
