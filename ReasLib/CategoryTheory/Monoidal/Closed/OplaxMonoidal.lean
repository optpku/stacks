module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
public import ReasLib.CategoryTheory.Monoidal.Closed.PullbackComparison
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Oplax-monoidal internal-Hom comparison

An oplax monoidal functor carries a canonical comparison from the image of an internal Hom to the
internal Hom of the images.  This is the orientation used by pullback functors, where the tensor
comparison is `F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.OplaxMonoidal

noncomputable section

universe uC vC uD vD

namespace CategoryTheory.Functor.OplaxMonoidal.InternalHom

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
  [BraidedCategory D] [MonoidalClosed D]
variable (F : C ⥤ D) [F.OplaxMonoidal]
variable [∀ X Y : C, IsIso (δ F X Y)]

/-- The evaluation map obtained by applying an oplax monoidal functor to source evaluation. -/
@[stacks 08I3 "oplax internal-Hom evaluation"]
noncomputable def evaluation (X Y : C) :
    F.obj ((ihom X).obj Y) ⊗ F.obj X ⟶ F.obj Y :=
  Functor.PullbackInternalHom.evaluation F
    (fun A B ↦ asIso (δ F A B)) X Y

/-- Remark 20.42.13 (08I3), generic owner: an oplax monoidal functor maps an internal Hom to the
internal Hom of the images. -/
@[stacks 08I3 "oplax internal-Hom comparison"]
noncomputable def comparison (X Y : C) :
    F.obj ((ihom X).obj Y) ⟶
      (ihom (F.obj X)).obj (F.obj Y) :=
  Functor.PullbackInternalHom.comparison F
    (fun A B ↦ asIso (δ F A B)) X Y

/-- The braided transpose of `comparison` is its defining oplax evaluation map. -/
@[stacks 08I3 "oplax internal-Hom comparison specification"]
theorem comparison_spec (X Y : C) :
    (braidedHomEquiv
        (F.obj ((ihom X).obj Y)) (F.obj X) (F.obj Y)).symm
      (comparison F X Y) =
      evaluation F X Y :=
  Functor.PullbackInternalHom.comparison_spec F
    (fun A B ↦ asIso (δ F A B)) X Y

end CategoryTheory.Functor.OplaxMonoidal.InternalHom
