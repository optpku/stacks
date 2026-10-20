/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap79.«79_12_0_2_FinitePart»
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Opens
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Boolean
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.CompactSupport
import StacksCheckRecall

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite
universe u

/- 79.12.0.2: For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`,
the finite-part assignment `T ↦ {(a, Z)}` is a functor
`(X/Y)_fin : (Sch/S)ᵒᵖ ⥤ Type u`. A pair over `T` is a morphism
`a : ofOver T ⟶ Y` over `S` together with an open `Z ⊂ |T ×_Y X|` such that
`pr₀|_Z : Z ⟶ T` is finite. Functoriality is `a' = a ∘ h` and
`Z' = (h × id_X)⁻¹(Z) = T' ×_T Z`. -/
@[stacks 04PD] #check (AlgebraicGeometry.AlgebraicSpace.finitePart :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    (Over S)ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.AlgebraicSpace.finitePart_obj_equiv :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (T : Over S),
    (finitePart f).obj (op T) ≃ FinitePart.Point f T)
