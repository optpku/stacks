/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits

/-! # Upper-universe sheafification for additive groups and commutative rings

Presheaves of additive commutative groups and commutative rings have sheafification
in the upper universe. For both coefficient categories, the morphisms inverted by
sheafification are precisely the locally bijective morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.CoefficientSheafification

/-- Sheafification exists for additive commutative group presheaves in the upper universe. -/
theorem additive {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{u + 1} := by
  infer_instance

/-- Sheafification exists for commutative ring presheaves in the upper universe. -/
theorem commRing {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    HasSheafify J CommRingCat.{u + 1} := by
  infer_instance

/-- Sheafification of additive commutative group presheaves in the upper universe
inverts precisely the locally bijective morphisms. -/
theorem additiveW {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
  infer_instance

/-- Sheafification of commutative ring presheaves in the upper universe
inverts precisely the locally bijective morphisms. -/
theorem commRingW {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective CommRingCat.{u + 1} := by
  infer_instance

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.CoefficientSheafification
