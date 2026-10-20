/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Sheafification
public import ReasLib.CategoryTheory.Limits.FiniteConnected.Preserves

/-!
# Colimits preserved by almost cocontinuous pushforward

The continuous pushforward of type-valued sheaves along an almost cocontinuous
functor preserves finite connected colimits.
-/

@[expose] public section

open CategoryTheory Limits

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor.IsAlmostCocontinuous

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- Continuous pushforward along an almost cocontinuous functor preserves finite connected
colimits of type-valued sheaves. Preservation of each finite connected shape is supplied by
`PreservesFiniteConnectedColimits.preservesColimitsOfShape`. -/
instance pushforwardContinuous_preservesFiniteConnectedColimits
    [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
    [K.WEqualsLocallyBijective (Type w)]
    [u.IsContinuous J K] [u.IsAlmostCocontinuous J K] :
    PreservesFiniteConnectedColimits
      (u.sheafPushforwardContinuous (Type w) J K) := sorry

end CategoryTheory.Functor.IsAlmostCocontinuous
