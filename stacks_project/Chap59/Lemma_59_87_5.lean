/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 59.87.5: if `f : X ⟶ S` is flat and locally of finite presentation with
geometrically reduced fibres, then étale inverse image preserves arbitrary products. -/
@[stacks 0EYR] #check
  (AlgebraicGeometry.Scheme.smallEtalePullback_sheafPullback_preservesProducts :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ P : S.Etaleᵒᵖ ⥤ Type (u + 1),
      (smallEtalePullback f).op.HasLeftKanExtension P]
    {J : Type (u + 1)},
    PreservesLimitsOfShape (Discrete J)
      ((smallEtalePullback f).sheafPullback (Type (u + 1))
        S.smallEtaleTopology X.smallEtaleTopology))
