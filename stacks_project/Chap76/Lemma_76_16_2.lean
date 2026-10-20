/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyEtale.EtaleLocal
import StacksCheckRecall

/-! Lemma 76.16.2: Formal étaleness is local on étale scheme charts. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 76.16.2 (1) -/
@[stacks 04GD] #check (AlgebraicGeometry.AlgebraicSpace.FormallyEtale.iff_etaleLocal :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.FormallyEtale f ↔
        AlgebraicGeometry.AlgebraicSpace.etaleLocal
          @AlgebraicGeometry.FormallyEtale f)

/- Lemma 76.16.2 (2) -/
@[stacks 04GD] #check (AlgebraicGeometry.AlgebraicSpace.FormallyEtale.iff_existsSurjectiveEtaleSchemeSquare :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y),
      AlgebraicGeometry.AlgebraicSpace.FormallyEtale f ↔
        AlgebraicGeometry.AlgebraicSpace.FormallyEtale.existsSurjectiveEtaleSchemeSquare f)
