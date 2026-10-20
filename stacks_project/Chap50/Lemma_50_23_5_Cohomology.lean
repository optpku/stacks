/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.Cohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpace
open SheafOfModules.RingedSite.ExteriorPower

noncomputable section

universe u

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) (f : X ⟶ S) (p q : ℕ)

#check (AlgebraicGeometry.Scheme.DeRham.Gysin.restriction i f p q :
  RingedSpace.moduleCohomology
        ((Scheme.Modules.toRingedSpace X).obj (sheaf X.𝒪 Ω[f.toShHom] p)) q ⟶
    RingedSpace.moduleCohomology
      ((Scheme.Modules.toRingedSpace X).obj
        ((Scheme.Modules.pushforward i).obj
          (sheaf Z.𝒪 Ω[(i ≫ f).toShHom] p))) q)

#check (AlgebraicGeometry.Scheme.DeRham.Gysin.relativeFormZeroOneCohomology f :
  RingedSpace.moduleCohomology
    ((Scheme.Modules.toRingedSpace X).obj (sheaf X.𝒪 Ω[f.toShHom] 0)) 0)

end
