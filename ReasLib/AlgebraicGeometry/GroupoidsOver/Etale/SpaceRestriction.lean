/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SmallEtaleComparison

/-! # Restriction from represented groupoid fibrations to small étale sites -/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.AlgebraicSpace

noncomputable section
universe u

namespace AlgebraicGeometry.GroupoidsOver
variable {S : Scheme.{u}}

/-- The tautological functor `u : F_étale ⥤ (S_F)_étale` is continuous for the
small étale topology of `F` and the associated étale topology of `S_F`. -/
instance smallEtaleToGroupoids_isContinuous (F : AlgebraicSpace S) :
    (smallEtaleToGroupoids F).IsContinuous
      (smallEtaleTopology F) F.toGroupoids.etaleTopology :=
  sorry

/-- The tautological functor `u : F_étale ⥤ (S_F)_étale` is cocontinuous for the
small étale topology of `F` and the associated étale topology of `S_F`. -/
instance smallEtaleToGroupoids_isCocontinuous (F : AlgebraicSpace S) :
    (smallEtaleToGroupoids F).IsCocontinuous
      (smallEtaleTopology F) F.toGroupoids.etaleTopology :=
  sorry

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

/-- Restriction of an étale sheaf on `S_F` to the small étale site of `F`,
i.e. `ℱ |_{F_étale} = i_F⁻¹ ℱ = π_{F,*} ℱ`. -/
def restrictEtale (F : AlgebraicSpace S) :
    Sheaf F.toGroupoids.etaleTopology (Type (u + 1)) ⥤
      Sheaf (smallEtaleTopology F) (Type (u + 1)) :=
  (GroupoidsOver.smallEtaleToGroupoids F).sheafPushforwardContinuous (Type (u + 1))
    (smallEtaleTopology F) F.toGroupoids.etaleTopology

/-- `restrictEtale` is continuous sheaf pushforward along `GroupoidsOver.smallEtaleToGroupoids`. -/
theorem restrictEtale_eq (F : AlgebraicSpace S) :
    restrictEtale F =
      (GroupoidsOver.smallEtaleToGroupoids F).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology F) F.toGroupoids.etaleTopology :=
  rfl

/-- Sections of a restricted sheaf on `F_étale` are the original sections on the
tautological object `u(U)`. -/
theorem restrictEtale_obj (F : AlgebraicSpace S)
    (ℱ : Sheaf F.toGroupoids.etaleTopology (Type (u + 1)))
    (U : smallEtaleSite F) :
    ((restrictEtale F).obj ℱ).obj.obj (op U) =
      ℱ.obj.obj (op ((GroupoidsOver.smallEtaleToGroupoids F).obj U)) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
