/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Functor

/-!
# Autoequivalences of finite-length module categories

This file records rigidity of linear autoequivalences of the category of finite-length modules
over a Noetherian local commutative ring.
-/

@[expose] public section

open CategoryTheory

universe u

namespace ModuleCat

/-- Every linear self-equivalence of the category of finite-length modules over a Noetherian
local commutative ring is naturally isomorphic to the identity functor. -/
theorem finiteLengthSelfEquivalenceIsoId
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (F : (Module.FiniteLengthDeterminant.moduleProperty.{u, u} A).FullSubcategory ⥤
      (Module.FiniteLengthDeterminant.moduleProperty.{u, u} A).FullSubcategory)
    [Functor.Linear A F] [F.IsEquivalence] :
    Nonempty (F ≅ 𝟭 _) := sorry

end ModuleCat
