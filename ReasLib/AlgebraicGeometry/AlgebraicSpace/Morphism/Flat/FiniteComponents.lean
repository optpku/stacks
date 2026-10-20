/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Finite irreducible components under flat locally finite type morphisms

A flat locally-of-finite-type morphism of algebraic spaces pulls back the
finite-irreducible-components-on-compact-opens property from its target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace HasFiniteIrreducibleComponentsOnCompactOpens

/-- A flat locally-of-finite-type morphism pulls back the property that
algebraic spaces have finitely many irreducible components on compact opens. -/
theorem of_flat_locallyOfFiniteType {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y] :
    HasFiniteIrreducibleComponentsOnCompactOpens X :=
  sorry

end HasFiniteIrreducibleComponentsOnCompactOpens

end AlgebraicGeometry.AlgebraicSpace
