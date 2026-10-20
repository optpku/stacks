/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Stalk.ClosedImmersion
import StacksCheckRecall

/-!
# Lemma 67.13.6

For a closed immersion of algebraic spaces, the small-étale stalk of a
pushed-forward sheaf of sets at the image geometric point is identified
with the stalk of the original sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.13.6: for a closed immersion `i : Z ⟶ X` of algebraic spaces over a
scheme `S`, a geometric point `zbar` of `Z`, and a sheaf `F` of sets on the
small étale site of `Z`, the stalk of `i_small,* F` at `zbar.map i` is
identified with the stalk of `F` at `zbar` by the canonical comparison.
These are the correctly typed stalk locations in the source proof: the direct image
is a sheaf on `X`, while `F` is a sheaf on `Z`. -/
@[stacks 0DK1] #check
  (AlgebraicGeometry.AlgebraicSpace.stalk_pushforward_closedImmersion :
    ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
      (F : Sheaf (smallEtaleTopology Z) (Type (u + 1))) (zbar : GeometricPoint Z),
      Function.Bijective (GeometricPoint.stalkPushforwardClosedImmersion i F zbar))

end AlgebraicGeometry.AlgebraicSpace
