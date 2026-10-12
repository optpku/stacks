/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Map
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalRing
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Functor.PresheafFiber.Map
public import Mathlib.AlgebraicGeometry.Spec

open CategoryTheory CategoryTheory.Limits Opposite CategoryOfElements
open AlgebraicGeometry

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- The map on étale local rings induced by a morphism of schemes and a geometric point. -/
noncomputable def etaleLocalRing.map {X S : Scheme.{u}} (f : X ⟶ S)
    (xbar : GeometricPoint X) :
    etaleLocalRing S (xbar.map f) →+* etaleLocalRing X xbar :=
  let sbar := xbar.map f
  let pS := GeometricPoint.toSmallEtalePoint sbar
  let pX := GeometricPoint.toSmallEtalePoint xbar
  let P := (S.smallEtaleToScheme.op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat)
  let Q := (X.smallEtaleToScheme.op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat)
  let θ : RingCat.Hom (RingCat.of (etaleLocalRing S sbar))
      (RingCat.of (etaleLocalRing X xbar)) :=
    colimit.desc ((CategoryOfElements.π pS.fiber).op ⋙ P)
      { pt := RingCat.of (etaleLocalRing X xbar)
        ι := {
          app := fun U =>
            let V := (smallEtalePullback f).obj U.unop.1
            let l : Spec (.of xbar.K) ⟶ V.left :=
              pullback.lift U.unop.2.left xbar.hom (by
                exact U.unop.2.w)
            let y : pX.fiber.obj V := Over.homMk l (by
              change pullback.lift U.unop.2.left xbar.hom U.unop.2.w ≫
                pullback.snd U.unop.1.hom f = xbar.hom
              exact pullback.lift_snd U.unop.2.left xbar.hom U.unop.2.w)
            ((forget₂ CommRingCat RingCat).map
                (Scheme.Γ.map (pullback.fst U.unop.1.hom f).op)) ≫
              pX.toPresheafFiber V y Q ≫ eqToHom (by rfl)
          naturality := fun _ _ _ => sorry } }
  RingCat.Hom.hom θ

/-- The induced local-ring map sends a germ on a pointed étale neighborhood to the
corresponding pulled-back germ at the image geometric point. -/
theorem etaleLocalRing.map_spec {X S : Scheme.{u}} (f : X ⟶ S)
    (xbar : GeometricPoint X) :
    ∀ (U : S.Etale) (x : (GeometricPoint.toSmallEtalePoint (xbar.map f)).fiber.obj U),
      (GeometricPoint.toSmallEtalePoint (xbar.map f)).toPresheafFiber U x
          ((S.smallEtaleToScheme.op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat)) ≫
        RingCat.ofHom (etaleLocalRing.map f xbar) =
      ((forget₂ CommRingCat RingCat).map (Scheme.Γ.map (pullback.fst U.hom f).op)) ≫
        (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber
          ((smallEtalePullback f).obj U)
          (Over.homMk (pullback.lift x.left xbar.hom (by
            exact x.w)) (by
              change _ ≫ pullback.snd U.hom f = xbar.hom
              exact pullback.lift_snd x.left xbar.hom x.w))
          ((X.smallEtaleToScheme.op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat)) := sorry

namespace StrictHenselization

/-- The canonical structural morphism from the strict henselization at a geometric point to its scheme. -/
def toScheme (S : Scheme.{u}) (s : GeometricPoint S) :
    strictHenselizationAt S s ⟶ S :=
  Spec.map (CommRingCat.ofHom (etaleLocalRing.fromZariskiStalk S s)) ≫
    S.fromSpecStalk s.image

/-- The canonical morphism between strict henselizations induced by a scheme morphism and a geometric point. -/
def map {X S : Scheme.{u}} (f : X ⟶ S)
    (xbar : GeometricPoint X) :
    strictHenselizationAt X xbar ⟶ strictHenselizationAt S (xbar.map f) :=
  Spec.map (CommRingCat.ofHom (etaleLocalRing.map f xbar))

end StrictHenselization

/-- The strict-henselization morphism is compatible with the structural morphisms to the base. -/
theorem StrictHenselization.map_toScheme {X S : Scheme.{u}} (f : X ⟶ S)
    (xbar : GeometricPoint X) :
    StrictHenselization.map f xbar ≫ StrictHenselization.toScheme S (xbar.map f) =
      StrictHenselization.toScheme X xbar ≫ f := sorry

/-- The canonical map between the two base changes of a strict henselization. -/
noncomputable def StrictHenselization.baseChangeMap {X S : Scheme.{u}} (f : X ⟶ S)
    (xbar : GeometricPoint X) {K : Type u} [Field K] [IsSepClosed K]
    (φ : Spec (CommRingCat.of K) ⟶ strictHenselizationAt S (xbar.map f)) :
    pullback (StrictHenselization.toScheme X xbar ≫ f) (φ ≫
        StrictHenselization.toScheme S (xbar.map f)) ⟶
      pullback (StrictHenselization.toScheme S (xbar.map f)) (φ ≫
        StrictHenselization.toScheme S (xbar.map f)) :=
  pullback.map (StrictHenselization.toScheme X xbar ≫ f)
    (φ ≫ StrictHenselization.toScheme S (xbar.map f))
    (StrictHenselization.toScheme S (xbar.map f))
    (φ ≫ StrictHenselization.toScheme S (xbar.map f))
    (StrictHenselization.map f xbar) (𝟙 _) (𝟙 _)
    (by simp [StrictHenselization.map_toScheme]) (by simp)

/-- The base-change map preserves the projection to the coefficient spectrum. -/
theorem StrictHenselization.baseChangeMap_snd {X S : Scheme.{u}} (f : X ⟶ S)
    (xbar : GeometricPoint X) {K : Type u} [Field K] [IsSepClosed K]
    (φ : Spec (CommRingCat.of K) ⟶ strictHenselizationAt S (xbar.map f)) :
    StrictHenselization.baseChangeMap f xbar φ ≫
        pullback.snd (StrictHenselization.toScheme S (xbar.map f))
          (φ ≫ StrictHenselization.toScheme S (xbar.map f)) =
      pullback.snd (StrictHenselization.toScheme X xbar ≫ f)
        (φ ≫ StrictHenselization.toScheme S (xbar.map f)) := sorry

end AlgebraicGeometry.Scheme

end
