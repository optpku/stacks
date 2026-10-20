/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CompactSupport.Compactification
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 63.3.10: extension by zero along an open immersion into a proper
scheme canonically identifies compactly supported global étale sections. -/
@[stacks 0F75] #check
  (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportCompactifyEquiv :
    ∀ {k : Type u} [Field k] {X Xbar : SchemeOverField k} (j : X ⟶ Xbar)
      [IsOpenImmersion j.left] [IsProper Xbar.hom]
      [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
      [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (etaleRestriction j.left).op.HasLeftKanExtension F]
      [HasWeakSheafify Xbar.left.smallEtaleTopology AddCommGrpCat.{u}]
      (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
      AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportSubgroup X F ≃+
        AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportSubgroup Xbar
          ((abelianExtensionByZero j.left).obj F))

/- Lemma 63.3.10: on the proper target, compactly supported sections of the
extension by zero are all its global sections. -/
@[stacks 0F75] #check
  (AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportCompactifyGlobalEquiv :
    ∀ {k : Type u} [Field k] {X Xbar : SchemeOverField k} (j : X ⟶ Xbar)
      [IsOpenImmersion j.left] [IsProper Xbar.hom]
      [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
      [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (etaleRestriction j.left).op.HasLeftKanExtension F]
      [HasWeakSheafify Xbar.left.smallEtaleTopology AddCommGrpCat.{u}]
      (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
      AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupportSubgroup X F ≃+
        ((abelianExtensionByZero j.left).obj F).obj.obj
          (op (AlgebraicGeometry.Scheme.Etale.globalEtale Xbar.left)))

end
