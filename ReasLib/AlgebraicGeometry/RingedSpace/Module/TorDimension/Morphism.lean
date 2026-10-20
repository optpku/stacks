/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.RingTheory.RingHom.TorDimension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor dimension of morphisms of ringed spaces

Finite Tor dimension for a morphism of ringed spaces is a stalkwise property of its structure
ring maps.  This owner is independent of flatness, so derived pullback criteria can import exactly
the hypothesis they use.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- A morphism of ringed spaces has finite Tor dimension at `x` when its stalk map at `x` does. -/
@[stacks 0GM7 "finite Tor dimension at a point"]
abbrev FiniteTorDimensionAt (x : X) : Prop :=
  (f.hom.stalkMap x).hom.HasFiniteTorDimension

/-- A morphism of ringed spaces has finite Tor dimension when all of its stalk maps do. -/
@[mk_iff, stacks 0GM7 "finite Tor dimension of a ringed-space morphism"]
class HasFiniteTorDimension : Prop where
  finiteTorDimensionAt (x : X) : FiniteTorDimensionAt f x

end RingedSpace.Hom
