/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.Module

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline

universe u

/- 60.10.0.2: for a morphism `f` of crystalline objects and a crystalline module sheaf `F`,
the comparison morphism `c_f` has type
`(Scheme.Modules.pullback f.thickening).obj (F.obj B) ⟶ F.obj A`. -/
@[stacks 07IQ] #check (CrystallineModuleSheaf.comparison :
    ∀ {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (g : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
          (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀)
    {A B : CRIS S I γ h_compatible X x₀}
    (f : CrystallineObject.Hom A B),
    (Scheme.Modules.pullback f.thickening).obj (F.obj B) ⟶ F.obj A)
