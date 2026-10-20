/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ProEtale.Comparison

/-!
# Small-to-big pro-étale comparison on abelian sheaves

The exact inverse image `π_S⁻¹` is provided by the shared pro-étale comparison
owner and used to compare big and small pro-étale cohomology.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable (S : Scheme.{u})

variable [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
variable [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
variable [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (ProEt.forget S).op.HasLeftKanExtension P]

#check (AlgebraicGeometry.Scheme.ProEt.piExact S :
  Sheaf (topology S) AddCommGrpCat.{u + 1} ⥤ₑ
    Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})

end AlgebraicGeometry.Scheme.ProEt
