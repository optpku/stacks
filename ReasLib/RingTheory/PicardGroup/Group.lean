/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.PicardGroup

@[expose] public section

universe u

namespace CommRing

/-- The bundled Picard group of a commutative semiring consists of isomorphism classes
of invertible modules, with multiplication induced by tensor product. -/
noncomputable def picardGroup (R : Type u) [CommSemiring R] : CommGrpCat.{u} :=
  CommGrpCat.of (Pic R)

end CommRing
