module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Limits.Fubini.DiagramOfCocones.Equivalence

/-!
# Colimit Fubini totalization and existence

This leaf transports colimit universal properties through cocone totalization and specializes
the construction to product-indexed diagrams.  Canonical comparison isomorphisms and their
component formulas live in the `Comparison` and `Computations` leaves.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Limits

open CategoryTheory Functor

variable {I : Type u₁} [Category.{v₁} I]
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u₃} [Category.{v₃} C]

namespace DiagramOfCocones

variable {F : I ⥤ J ⥤ C} (D : DiagramOfCocones F)

/-- Totalization preserves colimit cocones when every row cocone of `D` is colimiting. -/
noncomputable def _root_.CategoryTheory.Limits.IsColimit.totalCocone
    (hD : ∀ i, IsColimit (D.obj i)) {c : Cocone D.coconePoints} (hc : IsColimit c) :
    IsColimit (D.totalCoconeFunctor.obj c) :=
  IsColimit.ofPreservesCoconeInitial (D.coconeEquivalence hD).functor hc
/- Proof strategy: transport cocone initiality along `D.coconeEquivalence hD`; its forward
functor is `D.totalCoconeFunctor`. -/

/-- A colimit totalization reflects that its outer cocone is colimiting when all rows are. -/
noncomputable def _root_.CategoryTheory.Limits.IsColimit.ofTotalCocone
    (hD : ∀ i, IsColimit (D.obj i)) {c : Cocone D.coconePoints}
    (hc : IsColimit (D.totalCoconeFunctor.obj c)) : IsColimit c :=
  IsColimit.ofReflectsCoconeInitial (D.coconeEquivalence hD).functor hc
/- Proof strategy: reflect cocone initiality along the forward functor of
`D.coconeEquivalence hD`. -/

/-- Under rowwise colimit hypotheses, the outer diagram has a colimit exactly when the
uncurried diagram has a colimit. -/
lemma hasColimit_iff_uncurry (hD : ∀ i, IsColimit (D.obj i)) :
    HasColimit D.coconePoints ↔ HasColimit (uncurry.obj F) := sorry
/- Proof strategy: unpack a `HasColimit` witness in each direction; use
`D.totalCoconeFunctor` and `D.coconePointsFunctor hD`, together with
`IsColimit.totalCocone` and `IsColimit.ofTotalCocone`, to transport universal properties. -/

variable {M : I × J ⥤ C} (D : DiagramOfCocones (curry.obj M))

/-- Curry-specialized totalization as a functor into cocones on the original product diagram. -/
def curryTotalFunctor : Cocone D.coconePoints ⥤ Cocone M :=
  D.totalCoconeFunctor ⋙ Cocone.precompose ((currying.symm.unitIso).app M).hom

/-- Colimiting rows identify outer cocones with cocones on the original product-indexed
diagram. -/
def curryEquivalence (hD : ∀ i, IsColimit (D.obj i)) :
    Cocone D.coconePoints ≌ Cocone M :=
  (D.coconeEquivalence hD).trans
    (Cocone.precomposeEquivalence ((currying.symm.unitIso).app M).symm)

/-- Curry-specialized totalization preserves colimit cocones. -/
noncomputable def _root_.CategoryTheory.Limits.IsColimit.totalCurry
    (hD : ∀ i, IsColimit (D.obj i)) {c : Cocone D.coconePoints} (hc : IsColimit c) :
    IsColimit (D.curryTotalFunctor.obj c) :=
  IsColimit.ofPreservesCoconeInitial (D.curryEquivalence hD).functor hc
/- Proof strategy: transport cocone initiality along
`D.curryEquivalence hD`, whose forward functor is the public curry totalization
functor. -/

/-- A colimit curry-specialized totalization reflects that its outer cocone is colimiting. -/
noncomputable def _root_.CategoryTheory.Limits.IsColimit.ofTotalCurry
    (hD : ∀ i, IsColimit (D.obj i)) {c : Cocone D.coconePoints}
    (hc : IsColimit (D.curryTotalFunctor.obj c)) : IsColimit c :=
  IsColimit.ofReflectsCoconeInitial (D.curryEquivalence hD).functor hc
/- Proof strategy: reflect cocone initiality along the forward functor of
`D.curryEquivalence hD`. -/

/-- For a product-indexed diagram with chosen row colimits, the outer diagram has a colimit
exactly when the original diagram has a colimit. -/
@[stacks 002M "rowwise colimit functor and total colimit exist together"]
lemma hasColimit_iff (hD : ∀ i, IsColimit (D.obj i)) :
    HasColimit D.coconePoints ↔ HasColimit M := sorry
/- Proof strategy: compose `hasColimit_iff_uncurry hD` with invariance of
`HasColimit` under the diagram isomorphism `(currying.symm.unitIso).app M`; this identifies
`uncurry.obj (curry.obj M)` with `M`. -/

end DiagramOfCocones

end CategoryTheory.Limits
