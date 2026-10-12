/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.ProperDescent

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.72.8: for a proper morphism of Noetherian schemes whose structure-sheaf
pushforward map is an isomorphism, whose fibers have dimension at most one, and whose
fiber structure sheaves have vanishing first cohomology, pullback on Picard groups is
injective and its range is exactly the classes restricting to zero on every fiber. -/
@[stacks 0E24]
#check (AlgebraicGeometry.Scheme.Hom.picardPullback_identifies_fiberwiseTrivial :
  ∀ {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y] [IsProper f]
    [IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
    (hH1 : ∀ y : Y,
      IsZero (Scheme.Modules.cohomology
        (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1)),
    Function.Injective (picardPullback f) ∧
      (picardPullback f).range = ⨅ y : Y, (picardPullback (f.fiberι y)).ker)

end AlgebraicGeometry.Scheme.Hom
