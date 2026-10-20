/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Extension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.19.3: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated algebraic
space. Let `U, V ⊂ X` be quasi-compact open subspaces. Let `b : V' ⟶ V` be a
`(U ∩ V)`-admissible blowup. Then there exists a `U`-admissible blowup `X' ⟶ X` whose
restriction to `V` is `V'`. -/
@[stacks 086D] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isAdmissibleBlowup_restrict_iso_of_isAdmissibleBlowup_inter :
    ∀ {S : Scheme.{u}} {X V' : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (U V : OpenSubspace X)
      [QuasiCompact U.ι] [QuasiCompact V.ι] (b : V' ⟶ V.X),
      IsAdmissibleBlowup (U.preimage V) b →
        ∃ (X' : AlgebraicSpace S) (π : X' ⟶ X),
          IsAdmissibleBlowup U π ∧
            Nonempty (Over.mk (pullback.snd π V.ι) ≅ Over.mk b))
