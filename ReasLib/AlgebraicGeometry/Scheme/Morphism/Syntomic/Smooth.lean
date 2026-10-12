/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import ReasLib.RingTheory.RingHom.Syntomic.Smooth
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Smooth Scheme Morphisms Are Syntomic

A smooth scheme morphism is locally standard smooth. Standard smooth ring maps are smooth, and
smooth ring maps are syntomic, so the standard smooth affine neighborhoods give the required
scheme-level syntomic witnesses.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- A smooth morphism of schemes is syntomic. -/
@[stacks 01VD "smooth morphisms are syntomic"]
theorem Smooth.syntomic (hf : Smooth f) : Syntomic f := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ :=
    @Smooth.exists_isStandardSmooth X Y f hf x
  refine ⟨⟨V, hV⟩, hx, ⟨⟨U, hU⟩, e, ?_⟩⟩
  exact hstd.smooth.syntomic

/-- Every smooth morphism carries the canonical syntomic instance. -/
@[stacks 01VD, instance]
instance instSyntomicOfSmooth [Smooth f] : Syntomic f :=
  Smooth.syntomic inferInstance

end AlgebraicGeometry
