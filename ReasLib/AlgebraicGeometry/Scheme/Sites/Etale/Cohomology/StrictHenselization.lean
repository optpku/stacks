/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Map
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

/-- Étale cohomology after strict-henselization base change is controlled by the
corresponding cohomology comparison over the strict henselization. -/
theorem strictHenselizationBaseChange_iff
    {X S : Scheme.{u}} (f : X ⟶ S) (xbar : GeometricPoint X)
    {K : Type u} [Field K] [IsSepClosed K]
    [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ Z : Scheme.{u}, HasExt.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [∀ {A B : Scheme.{u}} (g : A ⟶ B) (G : B.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
      (smallEtalePullback g).op.HasLeftKanExtension G]
    (φ : Spec (CommRingCat.of K) ⟶ strictHenselizationAt S (xbar.map f))
    (F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (q : ℕ) :
    let sbar := xbar.map f
    let πS := StrictHenselization.toScheme S sbar
    let g := StrictHenselization.map f xbar
    let B := pullback πS (φ ≫ πS)
    let G := ((smallEtalePullback (pullback.snd πS (φ ≫ πS))).sheafPullback
      AddCommGrpCat.{u} (Spec (CommRingCat.of K)).smallEtaleTopology B.smallEtaleTopology).obj F
    IsIso (cohomologyPullback (StrictHenselization.baseChangeMap f xbar φ) G q) ↔
      IsIso (cohomologyPullback (pullback.snd g φ) F q) := sorry

end AlgebraicGeometry.Scheme.Etale

end
