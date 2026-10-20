/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Vanishing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cech acyclicity of pushforwards of injective module sheaves

This leaf owns the source-independent direct-image consequence of injectivity.  The reusable
object property is `ModuleCech.IsAcyclic`; degreewise vanishing is exposed as an ordinary theorem
rather than as an instance.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

namespace ModuleCech

variable {X Y : RingedSpace.{u}}

/-- The direct image of an injective module sheaf is Cech-acyclic. -/
@[stacks 01EX "pushforwards of injective modules are Cech-acyclic"]
theorem pushforward_isAcyclic_of_injective
    (f : X ⟶ Y) (ℐ : X.Modules) [Injective ℐ] :
    IsAcyclic ((Hom.pushforward f).obj ℐ) := sorry

/-- Positive-degree Cech cohomology of the direct image of an injective module sheaf is zero. -/
@[stacks 01EX "positive-degree Cech cohomology of an injective pushforward"]
theorem isZero_pushforward_of_injective
    (f : X ⟶ Y) (ℐ : X.Modules) [Injective ℐ]
    {i : Type u} (𝒱 : i → Opens Y.carrier) (p : ℕ) (hp : 0 < p) :
    IsZero (moduleCechCohomology 𝒱 ((Hom.pushforward f).obj ℐ) p) := sorry



end ModuleCech

end AlgebraicGeometry.RingedSpace

end
