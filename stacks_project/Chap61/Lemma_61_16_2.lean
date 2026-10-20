/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.PullbackSections
import StacksCheckRecall

/-!
# Lemma 61.16.2

On an affine weakly contractible object of the small pro-étale site, sections of
the Type-valued inverse image along `smallProetalePullback` are the colimit of
sections of the original sheaf along morphisms over the target.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

#check (AlgebraicGeometry.Scheme.ProEt.sheafPullback_fromColimit :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify (topology X) (Type (u + 1))]
    [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1),
      (smallProetalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf (topology Y) (Type (u + 1))) (W : X.ProEt)
    [(smallProetalePullback f).op.HasPointwiseLeftKanExtension F.obj],
    colimit (CostructuredArrow.proj (smallProetalePullback f).op (op W) ⋙ F.obj) ⟶
      (((smallProetalePullback f).sheafPullback (Type (u + 1))
          (topology Y) (topology X)).obj F).obj.obj (op W))

/- Lemma 61.16.2: if `f : X ⟶ Y` is a morphism of schemes and `F` is a sheaf of
sets on `Y.ProEt`, then for an affine weakly contractible object `W` of
`X.ProEt` one has `f_small⁻¹ F(W) = colim_{W ⟶ V} F(V)`, where the colimit runs
over morphisms `W ⟶ V` over `Y` with `V` in `Y.ProEt`. -/
@[stacks 0F64] #check (AlgebraicGeometry.Scheme.ProEt.sheafPullback_fromColimit_isIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify (topology X) (Type (u + 1))]
    [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1),
      (smallProetalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf (topology Y) (Type (u + 1))) (W : X.ProEt)
    [IsAffine W.left] [(topology X).IsWeaklyContractible W]
    [(smallProetalePullback f).op.HasPointwiseLeftKanExtension F.obj],
    IsIso (AlgebraicGeometry.Scheme.ProEt.sheafPullback_fromColimit f F W))

#check (AlgebraicGeometry.Scheme.ProEt.sheafPullback_fromColimit_ι :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify (topology X) (Type (u + 1))]
    [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1),
      (smallProetalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf (topology Y) (Type (u + 1))) (W : X.ProEt)
    [(smallProetalePullback f).op.HasPointwiseLeftKanExtension F.obj]
    (g : CostructuredArrow (smallProetalePullback f).op (op W)),
    colimit.ι (CostructuredArrow.proj (smallProetalePullback f).op (op W) ⋙ F.obj) g ≫
        AlgebraicGeometry.Scheme.ProEt.sheafPullback_fromColimit f F W =
      ((smallProetalePullback f).op.leftKanExtensionUnit F.obj).app g.left ≫
        ((smallProetalePullback f).op.leftKanExtension F.obj).map g.hom ≫
          (toSheafify (topology X)
              ((smallProetalePullback f).op.lan.obj F.obj)).app (op W) ≫
            ((Functor.sheafPullbackConstruction.sheafPullbackIso
                (smallProetalePullback f) (Type (u + 1)) (topology Y)
                (topology X)).inv.app F).hom.app (op W))

#check (AlgebraicGeometry.Scheme.ProEt.bijective_sheafPullback_fromColimit :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify (topology X) (Type (u + 1))]
    [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1),
      (smallProetalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf (topology Y) (Type (u + 1))) (W : X.ProEt)
    [IsAffine W.left] [(topology X).IsWeaklyContractible W]
    [(smallProetalePullback f).op.HasPointwiseLeftKanExtension F.obj],
    Function.Bijective (AlgebraicGeometry.Scheme.ProEt.sheafPullback_fromColimit f F W))

end AlgebraicGeometry.Scheme.ProEt
