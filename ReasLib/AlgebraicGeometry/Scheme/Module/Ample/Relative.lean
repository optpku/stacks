/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative ampleness of scheme modules

This file owns relative ampleness for a module over a morphism of schemes.  It
builds on the absolute ampleness object property and the canonical tensor
product on scheme modules.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/-- Restrict a module to the preimage of an open subscheme of the base. -/
@[stacks 01VR "module restriction to a base-open preimage"]
abbrev restrictToBasePreimage
    (f : X ⟶ S) (L : X.Modules) (V : S.Opens) :
    (f ⁻¹ᵁ V).toScheme.Modules :=
  L.restrict ((f ⁻¹ᵁ V).ι)

/-- The restriction of a module to a base-open preimage is ample. -/
@[stacks 01VR "ampleness on a base-open preimage"]
def IsAmpleOnBasePreimage (f : X ⟶ S) (L : X.Modules) (V : S.Opens) : Prop :=
  Scheme.Modules.isAmpleObject (restrictToBasePreimage f L V)

/-- A module is relatively ample over `f` when `f` is quasi-compact and its restriction to the
preimage of every affine base open is ample. -/
@[stacks 01VH "relatively ample module"]
class RelativelyAmple (f : X ⟶ S) (L : X.Modules) : Prop where
  /-- The module is invertible on the source. -/
  invertible : Scheme.Modules.Invertible L
  /-- The structure morphism is quasi-compact. -/
  quasiCompact : QuasiCompact f
  /-- The restriction over each affine base open is ample. -/
  isAmpleOnAffinePreimage :
    ∀ U : S.affineOpens, IsAmpleOnBasePreimage f L (U : S.Opens)

attribute [instance] RelativelyAmple.invertible

/-- Relative ampleness is equivalent to invertibility, quasi-compactness of the morphism, and
ampleness on the preimage of every affine open of the base. -/
theorem RelativelyAmple.iff :
    RelativelyAmple f L ↔
      Scheme.Modules.Invertible L ∧ QuasiCompact f ∧
        ∀ U : S.affineOpens, IsAmpleOnBasePreimage f L (U : S.Opens) := sorry

/-- A relatively ample module is invertible for the canonical tensor product. -/
@[stacks 01VH "explicit invertibility of a relatively ample module"]
theorem RelativelyAmple.isInvertible
    (h : RelativelyAmple f L) :
    Scheme.Modules.Invertible L := sorry

/-- The restriction over a bundled affine open of the base is ample. -/
@[stacks 01VH "relative ampleness on an affine base open"]
theorem RelativelyAmple.isAmpleOnAffineOpen
    (h : RelativelyAmple f L) (U : S.affineOpens) :
    IsAmpleOnBasePreimage f L U.1 := sorry

/-- The restriction of a relatively ample module to a specified affine base-open preimage is
ample. -/
@[stacks 01VH "relative ampleness on an affine preimage"]
theorem RelativelyAmple.isAmpleOnPreimage
    (h : RelativelyAmple f L) (U : S.Opens) (hU : IsAffineOpen U) :
    IsAmpleOnBasePreimage f L U := sorry

/-- A morphism carrying some relatively ample module is separated. -/
theorem isSeparated_of_exists_relativelyAmple
    {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∃ L : X.Modules, RelativelyAmple f L) :
    IsSeparated f := sorry

/-- A relatively ample module makes its structure morphism separated. -/
theorem RelativelyAmple.isSeparated
    (h : RelativelyAmple f L) :
    IsSeparated f := sorry

end

end AlgebraicGeometry
