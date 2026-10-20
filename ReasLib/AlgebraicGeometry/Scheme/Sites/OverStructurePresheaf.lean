/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Over

/-!
# The structure presheaf on schemes over a scheme

This module defines the commutative-ring-valued presheaf of global sections on
the category of schemes over a fixed scheme.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The structure presheaf on the category of schemes over `S`, obtained by
taking global sections of the underlying scheme. -/
abbrev overStructurePresheaf (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Over.forget S).op ⋙ Scheme.Γ

/-- The value of the structure presheaf over `S` at `U` is the ring of global
sections of the underlying scheme of `U`. -/
theorem overStructurePresheaf_obj (S : Scheme.{u}) (U : Over S) :
    S.overStructurePresheaf.obj (op U) = Γ(U.left, ⊤) := sorry

/-- For every scheme `S`, the global-sections presheaf on schemes over `S`,
viewed as a `RingCat`-valued presheaf, is a sheaf for the fpqc topology. -/
theorem overStructurePresheaf_isSheaf_fpqc (S : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      (S.overStructurePresheaf ⋙ forget₂ CommRingCat RingCat) := sorry

end AlgebraicGeometry.Scheme
