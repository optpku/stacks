/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.AffineCriterion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 56.6.5: a quasi-compact and quasi-separated scheme whose category of
quasi-coherent modules is equivalent to modules over a commutative ring is affine. -/
@[stacks 0GPI]
#check (AlgebraicGeometry.Scheme.QCoh.isAffine_of_moduleEquivalence :
  ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X],
    (∃ (R : Type u) (_ : CommRing R),
      Nonempty (Scheme.QCoh X ≌ ModuleCat.{u} R)) → IsAffine X)
