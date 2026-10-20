/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.OpenImmersion
import StacksCheckRecall

/-! # Canonical injectivity of finite-part sheaves along open immersions -/

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits Opposite

universe u

/- Lemma 79.12.2. An open immersion over the target induces a canonical injective
map of finite-part fppf sheaves, sending each pair `(a, Z)` to `(a, j(Z))`. -/
@[stacks 04PF] #check (AlgebraicGeometry.AlgebraicSpace.instMono_finitePartOpenMap :
  ∀ {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y} {f : X ⟶ Y}
    (j : X' ⟶ X) [IsOpenImmersion j] (hcomm : j ≫ f = f'),
    Mono (finitePartOpenMap j hcomm))

#check (AlgebraicGeometry.AlgebraicSpace.finitePartOpenMap_injective :
  ∀ {S : Scheme.{u}} {X' X Y : AlgebraicSpace S} {f' : X' ⟶ Y} {f : X ⟶ Y}
    (j : X' ⟶ X) [IsOpenImmersion j] (hcomm : j ≫ f = f') (T : (Over S)ᵒᵖ),
    Function.Injective fun (p : FinitePart.Point f' T.unop) ↦
      FinitePart.Point.map j hcomm p)
