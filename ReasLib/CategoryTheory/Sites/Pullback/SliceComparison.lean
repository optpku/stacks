module
public import ReasLib.CategoryTheory.Functor.KanExtension.OverIndex
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Restriction
@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
universe u v u' v' w z
namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [F.IsContinuous J K] [HasBinaryProducts C] [HasBinaryProducts D]
variable [PreservesLimitsOfShape (Discrete WalkingPair) F]
variable (A : Type w) [Category.{z} A] (V : C)
variable [HasWeakSheafify J A] [HasWeakSheafify K A]
variable [HasWeakSheafify (J.over V) A] [HasWeakSheafify (K.over (F.obj V)) A]
variable [(Over.post F).IsContinuous (J.over V) (K.over (F.obj V))]
variable [∀ P : Cᵒᵖ ⥤ A, F.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseLeftKanExtension P]
variable [∀ P : (Over V)ᵒᵖ ⥤ A, (Over.post F).op.HasLeftKanExtension P]
variable [∀ P : (Over V)ᵒᵖ ⥤ A, (Over.post F).op.HasPointwiseLeftKanExtension P]
variable [∀ P : (Over (F.obj V))ᵒᵖ ⥤ A,
    (Over.forget (F.obj V)).op.HasPointwiseRightKanExtension P]

/-- Sheaf inverse image commutes with restriction to a slice through actual Kan maps. -/
def sheafPullbackSliceIso (P : Sheaf J A) :
    ((F.sheafPullback A J K).obj P).over (F.obj V) ≅
      ((Over.post F).sheafPullback A (J.over V) (K.over (F.obj V))).obj (P.over V) := by
  let Q := P.obj
  let e := overKanIso F V Q
  exact ((K.overPullback A (F.obj V)).mapIso
      ((sheafPullbackConstruction.sheafPullbackIso F A J K).app P)) ≪≫
    ((Over.forget (F.obj V)).pushforwardContinuousSheafificationCompatibility
      A (K.over (F.obj V)) K).symm.app (F.op.leftKanExtension Q) ≪≫
    (presheafToSheaf (K.over (F.obj V)) A).mapIso e.symm ≪≫
    ((sheafPullbackConstruction.sheafPullbackIso (Over.post F) A (J.over V) (K.over (F.obj V))).app (P.over V)).symm

/-- Inverse image on the slice retains the same constant coefficient object. -/
def constantSheafPullbackSliceIso (E : A) :
    ((Over.post F).sheafPullback A (J.over V) (K.over (F.obj V))).obj
      ((constantSheaf (J.over V) A).obj E) ≅
        (constantSheaf (K.over (F.obj V)) A).obj E := by
  let ht : IsTerminal (Over.mk (𝟙 V)) := Over.mkIdTerminal
  let ht' : IsTerminal ((Over.post F).obj (Over.mk (𝟙 V))) :=
    IsTerminal.ofIso Over.mkIdTerminal (Over.isoMk (Iso.refl _) (by sorry))
  exact (((constantSheafAdj (J.over V) A ht).comp
      ((Over.post F).sheafAdjunctionContinuous A (J.over V) (K.over (F.obj V)))).leftAdjointUniq
        (constantSheafAdj (K.over (F.obj V)) A ht')).app E

/-- A supplied constant chart pulls back by the specified slice comparison. -/
def pulledConstantChartIso (P : Sheaf J A) (E : A)
    (e : P.over V ≅ (constantSheaf (J.over V) A).obj E) :
    ((F.sheafPullback A J K).obj P).over (F.obj V) ≅
      (constantSheaf (K.over (F.obj V)) A).obj E :=
  sheafPullbackSliceIso F J K A V P ≪≫
    ((Over.post F).sheafPullback A (J.over V) (K.over (F.obj V))).mapIso e ≪≫
    constantSheafPullbackSliceIso F J K A V E

end CategoryTheory.Functor
