/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Representability of group algebraic spaces over fields

A separated group algebraic space over a field is a scheme over the original
field. Representability after base change to the algebraic closure and the
locally finite type case are also recorded.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- A separated group algebraic space over a field becomes a scheme after base
change to the algebraic closure of the field. -/
@[stacks 0B8E, instance]
theorem isScheme_baseChange_algebraicClosure {k : Type u} [Field k]
    (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
    [AlgebraicSpace.IsSeparated G.X.left] :
    AlgebraicSpace.IsScheme
      (AlgebraicSpace.baseChange (FieldExtension.specMap k (AlgebraicClosure k)) G.X.left) := sorry

/-- A separated group algebraic space locally of finite type over a field is a
scheme. -/
@[stacks 0B8F, instance]
theorem isScheme_of_isSeparated_locallyOfFiniteType {k : Type u} [Field k]
    (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
    [AlgebraicSpace.IsSeparated G.X.left]
    [AlgebraicSpace.LocallyOfFiniteType (SchemeRealization.toBase G.X.left)] :
    AlgebraicSpace.IsScheme G.X.left := sorry

/-- A separated group algebraic space over a field is a scheme. -/
@[stacks 0B8G, instance]
theorem isScheme_of_isSeparated {k : Type u} [Field k]
    (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
    [AlgebraicSpace.IsSeparated G.X.left] :
    AlgebraicSpace.IsScheme G.X.left := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
