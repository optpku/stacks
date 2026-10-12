/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Action
public import ReasLib.CategoryTheory.Sites.Torsor.IsoClasses

/-!
# The pseudo-torsor of infinitesimal deformations

The additive sheaf of infinitesimal parameters acts simply transitively on compatible local
deformations, expressed multiplicatively as a sheaf-valued pseudo-torsor.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Deformation

variable {S X X' Y Y' : Scheme.{u}}

/-- The sectionwise multiplicative presentation of the additive deformation action. -/
@[implicit_reducible]
noncomputable def mulAction (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens) :
    MulAction
      ((CategoryTheory.Sheaf.toSheafOfGroups (parameterSheaf S i a)).1.obj (op U'))
      ((sheaf S i j a A).1.obj (op U')) where
  smul := act S i j a A U'
  one_smul := act_zero S i j a A U'
  mul_smul := act_add S i j a A U'

/-- The deformation sheaf as a pseudo-torsor under the pushed-forward internal-Hom sheaf. -/
noncomputable def pseudoTorsor (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) :
    CategoryTheory.Sheaf.PseudoTorsor
      (CategoryTheory.Sheaf.toSheafOfGroups (parameterSheaf S i a)) where
  carrier := sheaf S i j a A
  mulAction := mulAction S i j a A
  act_naturality f θ s := act_naturality S i j a A f.le θ s
  isPretransitive U :=
    @MulAction.IsPretransitive.mk _ _ (mulAction S i j a A U).toSMul
      (fun x y ↦ @AddAction.IsPretransitive.exists_vadd_eq _ _
        (addAction S i j a A U).toVAdd (act_isPretransitive S i j a A U) x y)
  isCancelSMul U :=
    @IsCancelSMul.mk _ _ (mulAction S i j a A U).toSMul
      (@IsLeftCancelSMul.mk _ _ (mulAction S i j a A U).toSMul
        (fun g x y h ↦ @IsLeftCancelVAdd.left_cancel' _ _
          (addAction S i j a A U).toVAdd
          (act_isCancelVAdd S i j a A U).toIsLeftCancelVAdd g x y h))
      (fun g h x eq ↦ @IsCancelVAdd.right_cancel' _ _
        (addAction S i j a A U).toVAdd (act_isCancelVAdd S i j a A U) g h x eq)

end AlgebraicGeometry.Scheme.Hom.Deformation
