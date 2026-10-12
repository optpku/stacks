/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
public import stacks_project.Chap61.Lemma_61_12_19_Pullback
import Mathlib.Tactic.CrossRefAttribute

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

/-- Comparison from the colimit of sections of `F` along morphisms `W ⟶ V` over
`Y` to the sections of the small pro-étale inverse image of `F` on `W`. -/
def sheafPullback_fromColimit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify (topology X) (Type (u + 1))]
    [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1),
      (smallProetalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf (topology Y) (Type (u + 1))) (W : X.ProEt)
    [IsAffine W.left] [(topology X).IsWeaklyContractible W]
    [(smallProetalePullback f).op.HasPointwiseLeftKanExtension F.obj] :
    colimit (CostructuredArrow.proj (smallProetalePullback f).op (op W) ⋙ F.obj) ⟶
      (((smallProetalePullback f).sheafPullback (Type (u + 1))
          (topology Y) (topology X)).obj F).obj.obj (op W) :=
  ((smallProetalePullback f).op.leftKanExtensionObjIsoColimit F.obj (op W)).inv ≫
    (toSheafify (topology X) ((smallProetalePullback f).op.lan.obj F.obj)).app (op W) ≫
      ((Functor.sheafPullbackConstruction.sheafPullbackIso (smallProetalePullback f)
          (Type (u + 1)) (topology Y) (topology X)).inv.app F).hom.app (op W)

/-- Lemma 61.16.2: if `f : X ⟶ Y` is a morphism of schemes and `F` is a sheaf of
sets on `Y.ProEt`, then for an affine weakly contractible object `W` of
`X.ProEt` one has `f_small⁻¹ F(W) = colim_{W ⟶ V} F(V)`, where the colimit runs
over morphisms `W ⟶ V` over `Y` with `V` in `Y.ProEt`. -/
@[stacks 0F64]
instance sheafPullback_fromColimit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify (topology X) (Type (u + 1))]
    [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1),
      (smallProetalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf (topology Y) (Type (u + 1))) (W : X.ProEt)
    [IsAffine W.left] [(topology X).IsWeaklyContractible W]
    [(smallProetalePullback f).op.HasPointwiseLeftKanExtension F.obj] :
    IsIso (sheafPullback_fromColimit f F W) :=
  sorry

/-- A morphism `W ⟶ V` over `Y` sends a section of `F` on `V` to the
corresponding section of the small pro-étale inverse image on `W`. -/
theorem sheafPullback_fromColimit_ι {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify (topology X) (Type (u + 1))]
    [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1),
      (smallProetalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf (topology Y) (Type (u + 1))) (W : X.ProEt)
    [IsAffine W.left] [(topology X).IsWeaklyContractible W]
    [(smallProetalePullback f).op.HasPointwiseLeftKanExtension F.obj]
    (g : CostructuredArrow (smallProetalePullback f).op (op W)) :
    colimit.ι (CostructuredArrow.proj (smallProetalePullback f).op (op W) ⋙ F.obj) g ≫
        sheafPullback_fromColimit f F W =
      ((smallProetalePullback f).op.leftKanExtensionUnit F.obj).app g.left ≫
        ((smallProetalePullback f).op.leftKanExtension F.obj).map g.hom ≫
          (toSheafify (topology X)
              ((smallProetalePullback f).op.lan.obj F.obj)).app (op W) ≫
            ((Functor.sheafPullbackConstruction.sheafPullbackIso
                (smallProetalePullback f) (Type (u + 1)) (topology Y)
                (topology X)).inv.app F).hom.app (op W) :=
  sorry

/-- Sections of the small pro-étale inverse image of a sheaf of sets are
bijective with the indicated colimit of sections, on affine weakly
contractible objects. -/
theorem bijective_sheafPullback_fromColimit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasWeakSheafify (topology X) (Type (u + 1))]
    [∀ P : Y.ProEtᵒᵖ ⥤ Type (u + 1),
      (smallProetalePullback f).op.HasLeftKanExtension P]
    (F : Sheaf (topology Y) (Type (u + 1))) (W : X.ProEt)
    [IsAffine W.left] [(topology X).IsWeaklyContractible W]
    [(smallProetalePullback f).op.HasPointwiseLeftKanExtension F.obj] :
    Function.Bijective (sheafPullback_fromColimit f F W) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
