/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Map
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.DirectImage.BaseChange

/-!
# Strict-henselization criterion for étale base change
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

/-- The morphism from the fibre over a strict henselization on the source to the
fibre over the strict henselization at its image geometric point. -/
def strictHenselizationFiberMap {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (x : GeometricPoint X) :
    pullback (StrictHenselization.toScheme X x ≫ f) g ⟶
      pullback (StrictHenselization.toScheme S (x.map f)) g :=
  pullback.map (StrictHenselization.toScheme X x ≫ f) g
    (StrictHenselization.toScheme S (x.map f)) g
    (StrictHenselization.map f x) (𝟙 T) (𝟙 S)
    ((Category.comp_id _).trans (StrictHenselization.map_toScheme f x).symm)
    ((Category.comp_id g).trans (Category.id_comp g).symm)

/-- The strict-henselization fibre comparison preserves the projection to the
scheme being base changed. -/
theorem strictHenselizationFiberMap_snd {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (x : GeometricPoint X) :
    strictHenselizationFiberMap f g x ≫
        pullback.snd (StrictHenselization.toScheme S (x.map f)) g =
      pullback.snd (StrictHenselization.toScheme X x ≫ f) g := sorry

section Cohomology

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ Z : Scheme.{u}, HasExt.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [∀ {A B : Scheme.{u}} (morphism : A ⟶ B),
      ((smallEtalePullback morphism).sheafPushforwardContinuous AddCommGrpCat.{u}
        B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]

/-- Pullback on étale cohomology along the strict-henselization fibre comparison,
with coefficients restricted from the scheme being base changed. The target
coefficients are the iterated inverse image of the original sheaf. -/
def strictHenselizationCohomologyMap {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (q : ℕ)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) (x : GeometricPoint X) :
    let πX := StrictHenselization.toScheme X x
    let πS := StrictHenselization.toScheme S (x.map f)
    let G := ((smallEtalePullback (pullback.snd πS g)).sheafPullback AddCommGrpCat.{u}
      T.smallEtaleTopology (pullback πS g).smallEtaleTopology).obj F
    G.H' q (globalEtale (pullback πS g)) ⟶
      (((smallEtalePullback (strictHenselizationFiberMap f g x)).sheafPullback
        AddCommGrpCat.{u} (pullback πS g).smallEtaleTopology
        (pullback (πX ≫ f) g).smallEtaleTopology).obj G).H'
          q (globalEtale (pullback (πX ≫ f) g)) :=
  cohomologyPullback (strictHenselizationFiberMap f g x)
    (((smallEtalePullback
      (pullback.snd (StrictHenselization.toScheme S (x.map f)) g)).sheafPullback
        AddCommGrpCat.{u} T.smallEtaleTopology
        (pullback (StrictHenselization.toScheme S (x.map f)) g).smallEtaleTopology).obj F) q

/-- The cohomology comparison is pullback along the strict-henselization fibre
map applied to the coefficient sheaf restricted along the projection to `T`. -/
theorem strictHenselizationCohomologyMap_def {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (q : ℕ)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) (x : GeometricPoint X) :
    strictHenselizationCohomologyMap f g q F x =
      cohomologyPullback (strictHenselizationFiberMap f g x)
        (((smallEtalePullback
          (pullback.snd (StrictHenselization.toScheme S (x.map f)) g)).sheafPullback
            AddCommGrpCat.{u} T.smallEtaleTopology
            (pullback (StrictHenselization.toScheme S (x.map f)) g).smallEtaleTopology).obj F)
        q := sorry

end Cohomology

/-- For a cartesian square with quasi-compact, quasi-separated vertical morphism,
ordinary higher-direct-image étale base change is invertible exactly when the
natural cohomology comparison on strict-henselization fibres is invertible at
every geometric point of the new base. -/
theorem higherDirectImage_isIso_iff_strictHenselization
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (cart : IsPullback h e f g) [QuasiCompact g] [QuasiSeparated g]
    [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ Z : Scheme.{u}, HasExt.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [∀ {A B : Scheme.{u}} (morphism : A ⟶ B),
      ((smallEtalePullback morphism).sheafPushforwardContinuous AddCommGrpCat.{u}
        B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
    [HasInjectiveResolutions (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    (q : ℕ) (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) :
    (∀ x : GeometricPoint X, IsIso (strictHenselizationCohomologyMap f g q F x)) ↔
      IsIso ((AlgebraicGeometry.Scheme.Etale.HigherDirectImage.baseChange
        g h e f cart.w.symm q).app F) := sorry

end AlgebraicGeometry.Scheme.Etale.BaseChange
