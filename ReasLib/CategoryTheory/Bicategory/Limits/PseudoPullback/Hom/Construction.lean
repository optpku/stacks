/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom.Basic

/-!
# Constructors for morphisms of readable pseudopullback cones

This leaf transports the generic `PseudoCone.homMk` and `PseudoCone.hom₂Mk` constructors to the
readable four-field cospan presentation. It owns only concrete morphism and `2`-morphism data;
their reduction and extensionality laws are in `Hom.Computations`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- Construct a morphism of readable pseudopullback cones from its apex map and arbitrary
comparison modification. The comparison is not required to be invertible. -/
@[stacks 003Q "constructor for a morphism of pseudopullback cones"]
def homMk {S T : PseudoPullbackCone f g} (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ⟶ S.toPseudoCone.π) : S ⟶ T :=
  InducedBicategory.mkHom (PseudoCone.homMk l e)

/-- Construct a readable pseudopullback-cone `2`-morphism from a cell between apex maps
satisfying the normalized comparison equation. -/
@[stacks 003Q "constructor for a 2-morphism of pseudopullback cones"]
def hom₂Mk {S T : PseudoPullbackCone f g} {u v : S ⟶ T}
    (η : map u ⟶ map v)
    (comm : (T.toPseudoCone.comparison S.pt).map η ≫ fac v = fac u) : u ⟶ v :=
  InducedBicategory.mkHom₂ (PseudoCone.hom₂Mk η comm)

/- Data audit (mathlib 4.32): `homMk` and `hom₂Mk` delegate their non-`Prop` data to the
generic `PseudoCone` constructors, and the induced-bicategory wrappers add no choices. Any
`sorryAx` dependency is confined to stored compatibility proof fields, not to apex maps,
comparison modifications, or apex `2`-cells. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
