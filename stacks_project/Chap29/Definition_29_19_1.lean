/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.J2
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Definition 29.19.1: Let `X` be a locally Noetherian scheme. We say `X` is J-2 if for every
morphism `Y ⟶ X` which is locally of finite type, the regular locus `Reg(Y)` is open in `Y`. -/
@[stacks 07R3] #check (AlgebraicGeometry.Scheme.IsJ2 : Scheme.{u} → Prop)

#check
  (AlgebraicGeometry.Scheme.isJ2_iff_forall_regularLocus_isOpen_of_locallyOfFiniteType :
    ∀ (X : Scheme.{u}) [IsLocallyNoetherian X],
      AlgebraicGeometry.Scheme.IsJ2 X ↔
        ∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ X) [LocallyOfFiniteType f],
          IsOpen (Reg(Y)))
