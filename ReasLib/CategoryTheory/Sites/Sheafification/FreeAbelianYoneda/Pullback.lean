module

public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelianYoneda.Weak
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelianYoneda.ULift
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Pullback
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pullback of sheafified free abelian representables

This leaf owns the canonical pullback isomorphism for the sheafified free abelian Yoneda
object. It is built from compatibility of left Kan extension with sheafification and the
canonical identity left-Kan-extension isomorphism.
-/

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

/-- Left Kan extension along the identity functor is canonically isomorphic to the original
functor. -/
noncomputable def identityLanIso
    (A : Type w) [Category A] (F : Cᵒᵖ ⥤ A)
    [∀ P : Cᵒᵖ ⥤ A, (𝟭 C).op.HasLeftKanExtension P] :
    ((𝟭 C).op.lan.obj F) ≅ F :=
  ((𝟭 C).op.lanAdjunction A).leftAdjointUniq Adjunction.id |>.app F

end CategoryTheory.Functor

namespace CategoryTheory.GrothendieckTopology.FreeAbelianYoneda

variable {C : Type u} [Category.{v} C]

/-- The canonical pullback isomorphism for a sheafified free abelian representable. -/
@[stacks 0EZC "free-abelian-representable pullback"]
noncomputable def pullbackIso
    {J K : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{v}]
    [HasWeakSheafify K AddCommGrpCat.{v}]
    [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{v}, (𝟭 C).op.HasLeftKanExtension P]
    [Functor.IsContinuous (𝟭 C) J K] (U : C) :
    obj K U ≅ ((𝟭 C).sheafPullback AddCommGrpCat J K).obj (obj J U) :=
  let P := CategoryTheory.FreeAbelianYoneda.obj U
  (presheafToSheaf K AddCommGrpCat).mapIso
      (Functor.identityLanIso AddCommGrpCat P).symm ≪≫
    (Functor.lanSheafificationIso (𝟭 C) J K).app P

end CategoryTheory.GrothendieckTopology.FreeAbelianYoneda

namespace CategoryTheory.GrothendieckTopology.FreeAbelianYoneda.ULift

variable {C : Type u} [Category.{v} C]

/-- The universe-raised free abelian representable commutes with pullback along the identity
functor between two topologies. -/
@[stacks 0EZC "universe-raised free-abelian-representable pullback"]
noncomputable def pullbackIso
    {J K : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{max w v}]
    [HasWeakSheafify K AddCommGrpCat.{max w v}]
    [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}, (𝟭 C).op.HasLeftKanExtension P]
    [Functor.IsContinuous (𝟭 C) J K] (U : C) :
    obj.{w} K U ≅ ((𝟭 C).sheafPullback AddCommGrpCat.{max w v} J K).obj (obj.{w} J U) :=
  let P := CategoryTheory.FreeAbelianYoneda.ULift.obj.{u, v, w} U
  (presheafToSheaf K AddCommGrpCat.{max w v}).mapIso
      (Functor.identityLanIso AddCommGrpCat.{max w v} P).symm ≪≫
    (Functor.lanSheafificationIso (𝟭 C) J K).app P

end CategoryTheory.GrothendieckTopology.FreeAbelianYoneda.ULift
