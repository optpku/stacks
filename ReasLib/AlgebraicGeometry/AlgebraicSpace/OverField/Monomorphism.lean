/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

/-!
# Monomorphisms of algebraic spaces over a field

Local finite type and local quasi-finiteness over a field descend along
monomorphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If a monomorphism of algebraic spaces over a field has target locally of
finite type and locally quasi-finite over the field, then its source is locally
of finite type and locally quasi-finite over the field. -/
theorem locallyQuasiFinite_over_field_of_mono {k : Type u} [Field k]
    {X Y : AlgebraicSpace (Spec (CommRingCat.of k))} (f : X ⟶ Y) [Mono f]
    [LocallyOfFiniteType (SchemeRealization.toBase Y)]
    [LocallyQuasiFinite (SchemeRealization.toBase Y)] :
    LocallyOfFiniteType (SchemeRealization.toBase X) ∧
      LocallyQuasiFinite (SchemeRealization.toBase X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
