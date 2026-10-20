/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Stalk

/-!
# Maps between fibre stalks

This leaf owns the local-ring morphism induced by a triangle of scheme
morphisms and its locality property.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The distinguished point of the fibre of `g` over `g(f(x))` obtained from
the fibre of `f ≫ g` is `g.asFiber (f(x))`. -/
theorem relativeFiberStalkMapAt_asFiber {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    (compFiberToBaseFiber f g (g (f x))) ((f ≫ g).asFiber x) =
      g.asFiber (f x) := sorry

/-- The local-ring map from the stalk of the fibre of `g` to the stalk of the
fibre of `f ≫ g` induced by the triangle `X ⟶ Y ⟶ S`. -/
noncomputable def relativeFiberStalkMapAt {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    fiberStalkAt g (f x) ⟶ fiberStalkAt (f ≫ g) x :=
  ((g.fiber (g (f x))).presheaf.stalkCongr
      (.of_eq (relativeFiberStalkMapAt_asFiber f g x).symm)).hom ≫
    (compFiberToBaseFiber f g (g (f x))).stalkMap ((f ≫ g).asFiber x)

/-- The induced map between fibre stalks is a local homomorphism. -/
instance relativeFiberStalkMapAt_isLocalHom {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    IsLocalHom (relativeFiberStalkMapAt f g x).hom := sorry

end AlgebraicGeometry.Scheme.Hom
