module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek.Basic
import StacksCheckRecall

/-!
# Definition 18.16.1

Lower shriek for abelian presheaves is left Kan extension; lower shriek for abelian sheaves is its
associated sheaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D)

section Presheaf

variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension P]

/- Definition 18.16.1 (1) (04BF): abelian-presheaf lower shriek is left Kan extension along
`u.op`. -/
@[stacks 04BF "presheaf lower shriek"]
#check (u.op.lan : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ Dᵒᵖ ⥤ AddCommGrpCat.{w})

end Presheaf

section Pointwise

variable (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) [u.op.HasPointwiseLeftKanExtension ℱ]
variable (V : Dᵒᵖ)

/- Definition 18.16.1 (2) (04BF): its value is the colimit over arrows `V ⟶ u(U)`. -/
@[stacks 04BF "pointwise colimit"]
#check (u.op.leftKanExtensionObjIsoColimit ℱ V :
  (u.op.leftKanExtension ℱ).obj V ≅
    colimit (CostructuredArrow.proj u.op V ⋙ ℱ))

end Pointwise

section Sheaf

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]
variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension P]
variable [HasWeakSheafify K AddCommGrpCat.{w}]

/- Definition 18.16.1 (3) (04BF): abelian-sheaf lower shriek is obtained by sheafifying the
presheaf lower shriek. -/
@[stacks 04BF "sheaf lower shriek"]
#check (Functor.sheafPullbackConstruction.sheafPullback
  u AddCommGrpCat.{w} J K :
    Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w})

end Sheaf

end CategoryTheory
