/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage.InverseSystem

/-!
# Typed compatibility checks for higher direct images
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {T U : Scheme.{u}} (f : U ⟶ T)
variable [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasInjectiveResolutions (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})]

#check (schemeHigherDirectImage f :
  Sheaf U.smallEtaleTopology AddCommGrpCat.{u} → ℕ →
    Sheaf T.smallEtaleTopology AddCommGrpCat.{u})

#check (schemeHigherDirectImageMap f :
  ∀ {G G' : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}}
    (morphism : G ⟶ G') (n : ℕ),
      schemeHigherDirectImage f G n ⟶ schemeHigherDirectImage f G' n)

end AlgebraicGeometry.Scheme.Etale

end
