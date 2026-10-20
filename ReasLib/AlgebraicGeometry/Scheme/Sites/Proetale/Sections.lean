module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Abelian
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.WeaklyContractible

/-!
# Sections of pro-étale inverse images

The adjunction unit gives a canonical comparison from sections of an abelian
sheaf to sections of its inverse image on a base change. For a closed immersion,
this comparison is an isomorphism on affine weakly contractible objects whose
points specialize into the base change.
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

/-- The canonical comparison from sections of an abelian sheaf on `U` to
sections of its inverse image on `U ×_X Z`, obtained from the adjunction unit. -/
def smallInverseImage_obj_to (F : Sheaf (topology X) AddCommGrpCat.{u + 1})
    (U : X.ProEt) :
    F.obj.obj (op U) ⟶
      ((smallInverseImage i).obj F).obj.obj
        (op ((smallProetalePullback i).obj U)) :=
  (((smallProetalePullback i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (topology X) (topology Z)).unit.app F).hom.app (op U) ≫
    (Functor.sheafPushforwardContinuousObjObjIso (smallProetalePullback i)
        AddCommGrpCat.{u + 1} ((smallInverseImage i).obj F) U).hom

/-- The comparison on sections is the adjunction unit at `U`, transported along
continuous sheaf pushforward. -/
theorem smallInverseImage_obj_to_eq (F : Sheaf (topology X) AddCommGrpCat.{u + 1})
    (U : X.ProEt) :
    smallInverseImage_obj_to i F U =
      (((smallProetalePullback i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
            (topology X) (topology Z)).unit.app F).hom.app (op U) ≫
        (Functor.sheafPushforwardContinuousObjObjIso (smallProetalePullback i)
            AddCommGrpCat.{u + 1} ((smallInverseImage i).obj F) U).hom :=
  rfl

/-- For a closed immersion `i : Z ⟶ X` and an affine weakly contractible object
`U` of `X.ProEt` whose every point specializes into `U ×_X Z`, the canonical
comparison on sections is an isomorphism for every abelian sheaf on `X.ProEt`. -/
theorem smallInverseImage_obj_to_isIso [IsClosedImmersion i] (U : X.ProEt)
    [IsAffine U.left] [(topology X).IsWeaklyContractible U]
    (hU : ∀ x : U.left,
      ∃ z : (pullback U.hom i : Scheme.{u}),
        x ⤳ (pullback.fst U.hom i) z)
    (F : Sheaf (topology X) AddCommGrpCat.{u + 1}) :
    IsIso (smallInverseImage_obj_to i F U) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
