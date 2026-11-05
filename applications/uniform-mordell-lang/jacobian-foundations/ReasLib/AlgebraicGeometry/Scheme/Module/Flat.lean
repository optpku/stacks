module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver

/-!
# Flat module sheaves over a scheme base

This module specializes relative flatness of module sheaves on ringed spaces to schemes. It uses
the canonical restricted module for the global predicate and exposes a pointwise predicate for
local arguments.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- A scheme module `ℱ` is flat over `S` at `x` when its stalk is flat over the local ring of `S`
at `f(x)`. -/
@[stacks 01U3]
abbrev flatOverAt
    (ℱ : X.Modules) (f : X ⟶ S) (x : X) : Prop :=
  SheafOfModules.flatOverAt ℱ f.toShHom x

/-- A scheme module is flat over `S` when its canonical restricted `f⁻¹𝒪_S`-module is flat. -/
@[stacks 01U3]
abbrev flatOver
    (ℱ : X.Modules) (f : X ⟶ S) : Prop :=
  SheafOfModules.flatOver ℱ f.toShHom

/-- The pointwise scheme predicate is ordinary flatness of the corresponding restricted module
sheaf at the source point. -/
@[stacks 01U3]
theorem flatOverAt_iff_relativeModule_isFlatAt
    (ℱ : X.Modules) (f : X ⟶ S) (x : X) :
    flatOverAt ℱ f x ↔
      (SheafOfModules.relativeModule ℱ f.toShHom).IsFlatAt x := sorry

/-- Flatness of a scheme module over its base is equivalent to the pointwise flatness condition
at every source point. -/
@[stacks 01U3]
theorem flatOver_iff_forall_flatOverAt
    (ℱ : X.Modules) (f : X ⟶ S) :
    flatOver ℱ f ↔ ∀ x : X, flatOverAt ℱ f x := sorry

end AlgebraicGeometry.Scheme.Modules
