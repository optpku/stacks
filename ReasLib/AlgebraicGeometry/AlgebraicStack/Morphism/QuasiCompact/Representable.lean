/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact

/-!
# Representable quasi-compact morphisms of algebraic stacks

For morphisms representable by algebraic spaces, quasi-compactness on
scheme-slice tests is equivalent to quasi-compactness after base change by
every quasi-compact algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A morphism of algebraic stacks representable by algebraic spaces is
quasi-compact on scheme-slice tests of algebraic spaces if and only if every
2-fibre product against a quasi-compact algebraic stack is quasi-compact. -/
@[stacks 050T]
theorem has_quasiCompact_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.QuasiCompact S) f ↔ AlgebraicStack.QuasiCompact f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
