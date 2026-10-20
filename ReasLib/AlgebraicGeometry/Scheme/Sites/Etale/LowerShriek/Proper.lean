/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Acyclicity
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek

/-!
# Proper morphisms: compact-support direct image equals pushforward
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

/-- The canonical inclusion of compact-support direct image into small-étale
pushforward along a proper scheme morphism is an isomorphism. -/
instance etaleLowerShriekι_isIso : IsIso (etaleLowerShriekι f) := sorry

/-- Every section of the small-étale pushforward along a proper morphism has
proper support over the base. -/
theorem hasProperSupport_of_isProper
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (σ : F.obj.obj (op ((smallEtalePullback f).obj V))) :
    HasProperSupport f F V σ :=
  sorry

/-- The comparison isomorphism `f_! ≅ f_*` for a proper morphism of schemes. -/
def etaleLowerShriekIso :
    etaleLowerShriek f ≅ etaleAbelianPushforward f :=
  asIso (etaleLowerShriekι f)

end AlgebraicGeometry.Scheme.Etale

end
