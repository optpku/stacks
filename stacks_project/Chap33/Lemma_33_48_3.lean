/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ZeroScheme
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped ENat

universe u

/-
Lemma 33.48.3: for a connected scheme proper over a field, the zero scheme of a regular section
of an ample invertible module is connected when every closed-point local ring has depth at least
two.
-/
@[stacks 0FD9] #check
  (AlgebraicGeometry.Scheme.Modules.IsAmple.connectedSpace_zeroScheme :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}} [ConnectedSpace X]
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (L : X.Modules) [L.Invertible] [Scheme.Modules.IsAmple L]
      (s : L.sections)
      (_ : RingedSpace.IsRegularSection L s)
      (_ : ∀ x : X, x ∈ closedPoints X →
        (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x)),
      ConnectedSpace (Scheme.zeroScheme L s))
