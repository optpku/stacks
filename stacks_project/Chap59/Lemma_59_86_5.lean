/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Stalk
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 59.86.5: canonical higher-direct-image étale base change is an isomorphism
exactly when its strict-henselization fibre-cohomology comparison is an isomorphism
at every geometric point of the new base. -/
@[stacks 0EZU] #check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.higherDirectImage_isIso_iff_strictHenselization :
    ∀ {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
      (cart : IsPullback h e f g) [QuasiCompact g] [QuasiSeparated g]
      [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
      [∀ Z : Scheme.{u}, HasExt.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
      [∀ {A B : Scheme.{u}} (morphism : A ⟶ B),
        ((smallEtalePullback morphism).sheafPushforwardContinuous AddCommGrpCat.{u}
          B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
      [HasInjectiveResolutions (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      (q : ℕ) (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}),
      (∀ x : GeometricPoint X,
        IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.strictHenselizationCohomologyMap
          f g q F x)) ↔
        IsIso ((AlgebraicGeometry.Scheme.Etale.HigherDirectImage.baseChange
          g h e f cart.w.symm q).app F))
