/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint

/-!
# Representability criteria for adjoints

Pointwise representability of the appropriate Hom-presheaves gives a left adjoint through
mathlib's canonical partial-adjoint owner.
-/

@[expose] public section

universe vC uC vD uD

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace partialRightAdjoint

/-- A chosen representation of `F.op ⋙ yoneda.obj Y.obj` is canonically isomorphic to the
representing object selected by the partial right adjoint of `F`. -/
noncomputable def iso {F : C ⥤ D} (Y : F.PartialRightAdjointSource) {X : C}
    (Q : (F.op ⋙ yoneda.obj Y.obj).RepresentableBy X) :
    X ≅ F.partialRightAdjointObj Y :=
  Q.uniqueUpToIso (F.op ⋙ yoneda.obj Y.obj).representableBy

/-- The forward comparison carries the chosen universal element to the universal element of
the partial right adjoint. -/
@[simp]
theorem iso.hom_apply {F : C ⥤ D} (Y : F.PartialRightAdjointSource) {X : C}
    (Q : (F.op ⋙ yoneda.obj Y.obj).RepresentableBy X) :
    F.partialRightAdjointHomEquiv (Y := Y) (iso Y Q).hom =
      Q.homEquiv (𝟙 X) := sorry

/-- The inverse comparison carries the partial right adjoint's universal element back to the
chosen universal element. -/
@[simp]
theorem iso.inv_apply {F : C ⥤ D} (Y : F.PartialRightAdjointSource) {X : C}
    (Q : (F.op ⋙ yoneda.obj Y.obj).RepresentableBy X) :
    Q.homEquiv (iso Y Q).inv =
      F.partialRightAdjointHomEquiv (Y := Y) (𝟙 _) := sorry

end partialRightAdjoint

/-- Lemma 4.24.2 (Stacks 0A8B): if every presheaf `X ↦ (u.obj X ⟶ Y)` is representable, then
`u` is a left adjoint. -/
@[stacks 0A8B]
theorem isLeftAdjoint_of_objwise_hom_isRepresentable (u : C ⥤ D)
    (h : ∀ Y : D, (u.op ⋙ yoneda.obj Y).IsRepresentable) :
    u.IsLeftAdjoint := sorry

/-- A `Type`-valued presheaf that is a right adjoint is representable. -/
@[stacks 07D7 "right adjoint bridge"]
theorem isRepresentable_of_isRightAdjoint
    {A : Type uC} [Category.{vC} A] (F : Aᵒᵖ ⥤ Type vC)
    [F.IsRightAdjoint] : F.IsRepresentable := sorry

end CategoryTheory.Functor
