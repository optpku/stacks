/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
public import stacks_project.Chap61.Lemma_61_17_3_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.25.5

If `i : Z ⟶ X` is a closed immersion and `U` is an affine weakly contractible
object of `X.ProEt` whose points all specialize into `U ×_X Z`, then inverse
image along `smallProetalePullback i` identifies sections of abelian sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {Z X : Scheme.{u}} (i : Z ⟶ X)
variable [HasSheafify (topology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (topology Z) AddCommGrpCat.{u + 1}]
variable [∀ P : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
  (smallProetalePullback i).op.HasLeftKanExtension P]

/-- The canonical comparison `F(U) ⟶ i_small⁻¹ F(U ×_X Z)` obtained from the
unit of `smallInverseImage i ⊣ smallPushforward i`. -/
def smallInverseImage_obj_to (F : Sheaf (topology X) AddCommGrpCat.{u + 1})
    (U : X.ProEt) :
    F.obj.obj (op U) ⟶
      ((smallInverseImage i).obj F).obj.obj
        (op ((smallProetalePullback i).obj U)) :=
  (((smallProetalePullback i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (topology X) (topology Z)).unit.app F).hom.app (op U) ≫
    (Functor.sheafPushforwardContinuousObjObjIso (smallProetalePullback i)
        AddCommGrpCat.{u + 1} ((smallInverseImage i).obj F) U).hom

/-- `smallInverseImage_obj_to` is the adjunction unit at `U`, transported along
continuous sheaf pushforward. -/
theorem smallInverseImage_obj_to_eq (F : Sheaf (topology X) AddCommGrpCat.{u + 1})
    (U : X.ProEt) :
    smallInverseImage_obj_to i F U =
      (((smallProetalePullback i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
            (topology X) (topology Z)).unit.app F).hom.app (op U) ≫
        (Functor.sheafPushforwardContinuousObjObjIso (smallProetalePullback i)
            AddCommGrpCat.{u + 1} ((smallInverseImage i).obj F) U).hom :=
  sorry

/-- Lemma 61.25.5: if `i : Z ⟶ X` is a closed immersion of schemes and `U` is
an affine weakly contractible object of `X.ProEt` such that every point of `U`
specializes to a point of `(smallProetalePullback i).obj U`, then
`smallInverseImage_obj_to i F U` is an isomorphism for every abelian sheaf
`F` on `X.ProEt`. -/
@[stacks 09AC]
theorem smallInverseImage_obj_to_isIso [IsClosedImmersion i] (U : X.ProEt)
    [IsAffine U.left] [(topology X).IsWeaklyContractible U]
    (hU : ∀ x : U.left,
      ∃ z : (pullback U.hom i : Scheme.{u}),
        x ⤳ (pullback.fst U.hom i) z)
    (F : Sheaf (topology X) AddCommGrpCat.{u + 1}) :
    IsIso (smallInverseImage_obj_to i F U) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
