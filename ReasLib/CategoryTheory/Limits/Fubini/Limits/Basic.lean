/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Limits.Fubini.DiagramOfCones.Equivalence

/-!
# Limit Fubini totalization and existence

This leaf transports limit universal properties through cone totalization and specializes the
construction to product-indexed diagrams.  Canonical comparison isomorphisms and their component
formulas live in the `Comparison` and `Computations` leaves.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Limits

open CategoryTheory Functor

variable {I : Type u₁} [Category.{v₁} I]
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u₃} [Category.{v₃} C]

namespace DiagramOfCones

variable {F : I ⥤ J ⥤ C} (D : DiagramOfCones F)

/-- Totalization preserves limit cones when every row cone of `D` is limiting. -/
noncomputable def _root_.CategoryTheory.Limits.IsLimit.totalCone
    (hD : ∀ i, IsLimit (D.obj i)) {c : Cone D.conePoints} (hc : IsLimit c) :
    IsLimit (D.totalConeFunctor.obj c) :=
  IsLimit.ofPreservesConeTerminal (D.coneEquivalence hD).functor hc
/- Proof strategy: transport cone terminality along `D.coneEquivalence hD`; its forward functor
is `D.totalConeFunctor`. -/

/-- A limit totalization reflects that its outer cone is limiting when all rows are. -/
noncomputable def _root_.CategoryTheory.Limits.IsLimit.ofTotalCone
    (hD : ∀ i, IsLimit (D.obj i)) {c : Cone D.conePoints}
    (hc : IsLimit (D.totalConeFunctor.obj c)) : IsLimit c :=
  IsLimit.ofReflectsConeTerminal (D.coneEquivalence hD).functor hc
/- Proof strategy: reflect cone terminality along the forward functor of
`D.coneEquivalence hD`. -/

/-- Under rowwise limit hypotheses, the outer diagram has a limit exactly when the uncurried
diagram has a limit. -/
lemma hasLimit_iff_uncurry (hD : ∀ i, IsLimit (D.obj i)) :
    HasLimit D.conePoints ↔ HasLimit (uncurry.obj F) := sorry
/- Proof strategy: unpack a `HasLimit` witness in each direction; use `D.totalConeFunctor` and
`D.conePointsFunctor hD`, together with `IsLimit.totalCone` and `IsLimit.ofTotalCone`, to
transport universal properties. -/

variable {M : I × J ⥤ C} (D : DiagramOfCones (curry.obj M))

/-- Curry-specialized totalization as a functor into cones on the original product diagram. -/
def curryTotalFunctor : Cone D.conePoints ⥤ Cone M :=
  D.totalConeFunctor ⋙ Cone.postcompose ((currying.symm.unitIso).app M).inv

/-- Limiting rows identify outer cones with cones on the original product-indexed diagram. -/
def curryEquivalence (hD : ∀ i, IsLimit (D.obj i)) :
    Cone D.conePoints ≌ Cone M :=
  (D.coneEquivalence hD).trans
    (Cone.postcomposeEquivalence ((currying.symm.unitIso).app M)).symm

/-- Curry-specialized totalization preserves limit cones. -/
noncomputable def _root_.CategoryTheory.Limits.IsLimit.totalCurry
    (hD : ∀ i, IsLimit (D.obj i)) {c : Cone D.conePoints} (hc : IsLimit c) :
    IsLimit (D.curryTotalFunctor.obj c) :=
  IsLimit.ofPreservesConeTerminal (D.curryEquivalence hD).functor hc
/- Proof strategy: transport cone terminality along `D.curryEquivalence hD`, whose
forward functor is the public curry totalization functor. -/

/-- A limit curry-specialized totalization reflects that its outer cone is limiting. -/
noncomputable def _root_.CategoryTheory.Limits.IsLimit.ofTotalCurry
    (hD : ∀ i, IsLimit (D.obj i)) {c : Cone D.conePoints}
    (hc : IsLimit (D.curryTotalFunctor.obj c)) : IsLimit c :=
  IsLimit.ofReflectsConeTerminal (D.curryEquivalence hD).functor hc
/- Proof strategy: reflect cone terminality along the forward functor of
`D.curryEquivalence hD`. -/

/-- For a product-indexed diagram with chosen row limits, the outer diagram has a limit exactly
when the original diagram has a limit. -/
@[stacks 002M "rowwise limit functor and total limit exist together"]
lemma hasLimit_iff (hD : ∀ i, IsLimit (D.obj i)) :
    HasLimit D.conePoints ↔ HasLimit M := sorry
/- Proof strategy: compose `hasLimit_iff_uncurry hD` with invariance of `HasLimit`
under the diagram isomorphism `(currying.symm.unitIso).app M`; this identifies
`uncurry.obj (curry.obj M)` with `M`. -/

end DiagramOfCones

end CategoryTheory.Limits
