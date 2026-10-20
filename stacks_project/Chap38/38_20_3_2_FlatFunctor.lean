/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.LocalAlgebra.Flattening

@[expose] public section

open CategoryTheory

universe u v w

variable (A : Type u) (B : Type v) (M : Type w)
variable [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [AddCommGroup M] [Module B M]

#check (LocalAlgCat.Flattening.functor A B M : LocalAlgCat.{v} A ⥤ Type u)
