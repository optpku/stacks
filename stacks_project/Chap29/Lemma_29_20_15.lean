/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Descent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 29.20.15: a locally finite type monomorphism of schemes is separated and locally
quasi-finite. -/
@[stacks 0CT8] #check
  (AlgebraicGeometry.locallyQuasiFinite_of_locallyOfFiniteType_of_mono :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [Mono f],
      LocallyQuasiFinite f)

#check
  (AlgebraicGeometry.IsSeparated.isSeparated_of_mono :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f], IsSeparated f)
