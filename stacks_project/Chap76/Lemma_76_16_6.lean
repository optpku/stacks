/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyEtale.Characterization
import StacksCheckRecall

/-!
# Characterizations of formally étale morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.16.6. Let S be a scheme and f : X ⟶ Y a morphism of algebraic
spaces over S. The following are equivalent:
(1) f is formally étale;
(2) f is formally unramified and the universal first-order thickening of X
    over Y is equal to X;
(3) f is formally unramified and C_{X/Y} = 0;
(4) Ω_{X/Y} = 0 and C_{X/Y} = 0.
The identity being universal expresses equality of the thickening with X.
Vanishing of relative differentials implies formal unramifiedness, ensuring
that the universal thickening defining the conormal sheaf exists. -/
@[stacks 0614] #check
  (AlgebraicGeometry.AlgebraicSpace.FormallyEtale.iff_isUniversalFirstOrder_id :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      FormallyEtale f ↔ FormallyUnramified f ∧ IsUniversalFirstOrder (𝟙 X) f)

#check
  (AlgebraicGeometry.AlgebraicSpace.FormallyEtale.iff_isZero_conormal :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      FormallyEtale f ↔ FormallyUnramified f ∧ isZeroConormal f)

#check
  (AlgebraicGeometry.AlgebraicSpace.FormallyEtale.iff_isZero_relativeDifferentials_and_conormal :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      FormallyEtale f ↔ IsZero (Ω[f]) ∧ isZeroConormal f)
