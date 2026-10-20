/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.SetTheoreticInvariant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

/-!
# Reduced pre-relations and invariant morphisms
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- A set-theoretically invariant morphism out of a reduced pre-relation is invariant when the
target is locally separated over the base. -/
theorem isInvariant_of_isSetTheoreticallyInvariant {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} [AlgebraicSpace.LocallySeparated X.hom] (P : PreRelation U)
    [AlgebraicSpace.IsReduced P.left.left] {φ : U ⟶ X}
    (hφ : P.IsSetTheoreticallyInvariant φ) : P.IsInvariantHom φ := sorry

/-- Under reducedness of the pre-relation and local separatedness of the target, invariance is
equivalent to set-theoretic invariance. -/
theorem isInvariant_iff_isSetTheoreticallyInvariant {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} [AlgebraicSpace.LocallySeparated X.hom] (P : PreRelation U)
    [AlgebraicSpace.IsReduced P.left.left] (φ : U ⟶ X) :
    P.IsInvariantHom φ ↔ P.IsSetTheoreticallyInvariant φ := sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
