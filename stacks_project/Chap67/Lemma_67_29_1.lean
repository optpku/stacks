/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Constructible
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.29.1 -/
@[stacks 0ECW] #check (AlgebraicGeometry.AlgebraicSpace.IsEtaleLocallyConstructible.preimage : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {E : Set (Points Y)}, IsEtaleLocallyConstructible E → IsEtaleLocallyConstructible (Points.map f ⁻¹' E))

end AlgebraicGeometry.AlgebraicSpace
