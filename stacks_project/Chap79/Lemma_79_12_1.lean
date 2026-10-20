/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Hom
import StacksCheckRecall

/-! # The finite-part functor is an fppf sheaf -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 79.12.1 (1): for an arbitrary morphism of algebraic spaces over a scheme,
the finite-part presheaf satisfies the fppf sheaf condition. -/
@[stacks 04PE] #check (AlgebraicGeometry.AlgebraicSpace.finitePart_isSheaf :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (finitePart f))

/- Lemma 79.12.1 (2): morphisms from any algebraic space to the finite-part sheaf
are canonically in bijection with pairs consisting of a morphism to the target
and an open of its fibre product whose projection is finite. -/
@[stacks 04PE] #check (AlgebraicGeometry.AlgebraicSpace.finitePart_homEquiv :
  ∀ {S : Scheme.{u}} {X Y T : AlgebraicSpace S} (f : X ⟶ Y),
    (toSmallSheaf T ⟶ FinitePart.sheaf f) ≃ FinitePart.Descended f T)

#check (AlgebraicGeometry.AlgebraicSpace.finitePart_homEquiv_apply :
  ∀ {S : Scheme.{u}} {X Y T : AlgebraicSpace S} (f : X ⟶ Y)
    (η : toSmallSheaf T ⟶ FinitePart.sheaf f),
    finitePart_homEquiv f η = FinitePart.Descended.ofHom (Sheaf.homEquiv η))

#check (AlgebraicGeometry.AlgebraicSpace.finitePart_homEquiv_ofOver :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (U : Over S),
    (toSmallSheaf (ofOver U) ⟶ FinitePart.sheaf f) ≃ FinitePart.Point f U)
