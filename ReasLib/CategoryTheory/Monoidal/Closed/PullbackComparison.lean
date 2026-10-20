module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback/internal-Hom comparison

This leaf owns the objectwise construction used when a functor is supplied with a tensor comparison
`F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B`.  It is deliberately independent of naturality or a chosen
monoidal instance; the stronger `Functor.OplaxMonoidal.InternalHom` API supplies those coherences
automatically when they are available.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe uC vC uD vD

namespace CategoryTheory.Functor.PullbackInternalHom

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [BraidedCategory C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
  [BraidedCategory D]

/-- The evaluation map transported across an objectwise tensor comparison, with the source
closed structure supplied as explicit data. -/
@[stacks 08I3 "explicit pullback internal-Hom evaluation"]
noncomputable def evaluationOf
    (H : MonoidalClosed C) (F : C ⥤ D)
    (tensorIso : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (X Y : C) :
    F.obj (((@MonoidalClosed.internalHom C _ _ H).obj (Opposite.op X)).obj Y) ⊗ F.obj X ⟶
      F.obj Y :=
  (tensorIso (((@MonoidalClosed.internalHom C _ _ H).obj (Opposite.op X)).obj Y) X).inv ≫
    F.map ((β_ (((@MonoidalClosed.internalHom C _ _ H).obj (Opposite.op X)).obj Y) X).hom ≫
      ((@MonoidalClosed.internalHomAdjunction₂ C _ _ H).adj X).counit.app Y)

/-- The pointwise pullback/internal-Hom comparison selected by explicit source and target closed
structures; no naturality is claimed from the objectwise family `tensorIso`. -/
@[stacks 08I3 "explicit pullback internal-Hom comparison"]
noncomputable def comparisonOf
    (H : MonoidalClosed C) (H' : MonoidalClosed D) (F : C ⥤ D)
    (tensorIso : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (X Y : C) :
    F.obj (((@MonoidalClosed.internalHom C _ _ H).obj (Opposite.op X)).obj Y) ⟶
      ((@MonoidalClosed.internalHom D _ _ H').obj (Opposite.op (F.obj X))).obj (F.obj Y) :=
  braidedHomEquivOf H'
    (F.obj (((@MonoidalClosed.internalHom C _ _ H).obj (Opposite.op X)).obj Y))
    (F.obj X) (F.obj Y)
    (evaluationOf H F tensorIso X Y)

/-- The braided transpose of the explicit-owner comparison is its transported evaluation map. -/
@[stacks 08I3 "explicit pullback internal-Hom comparison specification"]
theorem comparisonOf_spec
    (H : MonoidalClosed C) (H' : MonoidalClosed D) (F : C ⥤ D)
    (tensorIso : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (X Y : C) :
    (braidedHomEquivOf H'
        (F.obj (((@MonoidalClosed.internalHom C _ _ H).obj (Opposite.op X)).obj Y))
        (F.obj X) (F.obj Y)).symm
      (comparisonOf H H' F tensorIso X Y) =
      evaluationOf H F tensorIso X Y :=
  Equiv.symm_apply_apply _ _

section Typeclass

variable [MonoidalClosed C] [MonoidalClosed D]

/-- The evaluation map transported across an objectwise tensor comparison. -/
@[stacks 08I3 "pullback internal-Hom evaluation"]
noncomputable def evaluation
    (F : C ⥤ D)
    (tensorIso : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (X Y : C) :
    F.obj ((ihom X).obj Y) ⊗ F.obj X ⟶ F.obj Y :=
  (tensorIso ((ihom X).obj Y) X).inv ≫
    F.map ((β_ ((ihom X).obj Y) X).hom ≫ (ihom.ev X).app Y)

/-- The pullback/internal-Hom comparison associated to an objectwise tensor comparison isomorphism. -/
@[stacks 08I3 "pullback internal-Hom comparison"]
noncomputable def comparison
    (F : C ⥤ D)
    (tensorIso : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (X Y : C) :
    F.obj ((ihom X).obj Y) ⟶
      (ihom (F.obj X)).obj (F.obj Y) :=
  braidedHomEquiv
    (F.obj ((ihom X).obj Y)) (F.obj X) (F.obj Y)
    (evaluation F tensorIso X Y)

/-- The braided transpose of `comparison` is its transported evaluation map. -/
@[stacks 08I3 "pullback internal-Hom comparison specification"]
theorem comparison_spec
    (F : C ⥤ D)
    (tensorIso : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (X Y : C) :
    (braidedHomEquiv
        (F.obj ((ihom X).obj Y)) (F.obj X) (F.obj Y)).symm
      (comparison F tensorIso X Y) =
      evaluation F tensorIso X Y :=
  Equiv.symm_apply_apply _ _

/- Uncurrying the comparison removes the source-order braiding used by `braidedHomEquiv` and
recovers the transported evaluation map. -/
@[stacks 08I3 "pullback internal-Hom uncurried specification"]
theorem comparison_uncurry
    (F : C ⥤ D)
    (tensorIso : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (X Y : C) :
    uncurry (comparison F tensorIso X Y) =
      (β_ (F.obj ((ihom X).obj Y)) (F.obj X)).inv ≫
        evaluation F tensorIso X Y := by
  rw [← cancel_epi (β_ (F.obj ((ihom X).obj Y)) (F.obj X)).hom,
    Iso.hom_inv_id_assoc,
    ← braidedHomEquiv_symm_apply, comparison_spec]

end Typeclass

end CategoryTheory.Functor.PullbackInternalHom
