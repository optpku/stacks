/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy
public import stacks_project.Chap46.Definition_46_3_2
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

/- Definition 46.5.1 - a sheaf of modules is adequate when one affine `τ`-cover
of the base has adequate affine-evaluation functors. -/
@[stacks 06VG] #check
  (SheafOfModules.IsAdequate (S := S) (τ := τ) :
    ((A : CommRingCat.{u}) →
      ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u})) →
      (RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S) →
        (A : CommRingCat.{u}) → (Scheme.Spec.obj (op A) ⟶ S) →
          Under A ⥤ AddCommGrpCat.{u}) →
      RingedSite.ModuleCat.{u} (StandardTopology.Big.ringedSite τ S) → Prop)

end SheafOfModules
