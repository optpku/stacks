/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.PicardGroup.Group
import StacksCheckRecall

@[expose] public section

open CommRing TensorProduct

universe u

section

variable (R : Type u) [CommRing R]

/- Definition 111.22.3: the class group of a ring `A`, also called the Picard group of `A`,
is the set `Pic A` of isomorphism classes of invertible `A`-modules endowed with a group
operation defined by tensor product. -/
@[stacks 078Q] #check (CommRing.picardGroup R : CommGrpCat.{u})

#check (inferInstance : CommGroup (Pic R))

variable (M N : Type*) [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] [Module.Invertible R M] [Module.Invertible R N]

#check (CommRing.Pic.mk R M : Pic R)
#check (CommRing.Pic.mk_eq_mk_iff :
  Pic.mk R M = Pic.mk R N ↔ Nonempty (M ≃ₗ[R] N))
#check (CommRing.Pic.mk_tensor :
  Pic.mk R (M ⊗[R] N) = Pic.mk R M * Pic.mk R N)

end
