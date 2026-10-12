/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.IteratedRelative.Basic
public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»
public import stacks_project.Chap64.Lemma_64_3_2_Pullback

/-!
# Geometric Frobenius on the small étale site

This leaf owns the small-étale site isomorphism `U ≅ U ×_{π_X} X` induced by
iterated relative Frobenius, together with the canonical identifications
`π_X⁻¹ F ≅ F` and `F ≅ (π_X)_* F` of abelian sheaves.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {p : ℕ} [Fact p.Prime]
variable {U X : Scheme.{u}} (f : U ⟶ X)
variable [Scheme.IsCharP X p]

/-- The structure morphism of a Frobenius-power twist of an étale morphism is
étale. -/
instance pPowerTwist_etale [Etale f] (n : ℕ) :
    Etale (pPowerTwist (p := p) f n).hom :=
  inferInstanceAs (Etale (pullback.snd f (absoluteFrobeniusPow p X n)))

/-- Relative Frobenius of a Frobenius-power twist of an étale morphism is an
isomorphism. -/
instance relativeFrobenius_pPowerTwist_isIso [Etale f] (n : ℕ) :
    IsIso (Hom.relativeFrobenius (p := p) (pPowerTwist (p := p) f n).hom) :=
  Hom.relativeFrobenius_isIso_of_etale (pPowerTwist (p := p) f n).hom

/-- Inverse of the underlying scheme morphism of iterated relative Frobenius of
an étale morphism, obtained by reversing successive relative-Frobenius steps. -/
def iteratedRelativeFrobeniusLeftInv [Etale f] :
    (n : ℕ) → (pPowerTwist (p := p) f n).left ⟶ U
  | 0 => pullback.fst f (absoluteFrobeniusPow p X 0)
  | n + 1 =>
      (pPowerTwistSuccIso (p := p) f n).inv.left ≫
        (pullback.congrHom rfl
            (absoluteFrobenius_eq_absoluteFrobeniusPow_one p X)).inv ≫
          CategoryTheory.inv
              (Hom.relativeFrobenius (p := p) (pPowerTwist (p := p) f n).hom) ≫
            iteratedRelativeFrobeniusLeftInv n

/-- The underlying scheme morphism of iterated relative Frobenius of an étale
morphism, as a scheme isomorphism. -/
def iteratedRelativeFrobeniusLeftIso [Etale f] (n : ℕ) :
    U ≅ (pPowerTwist (p := p) f n).left where
  hom := (iteratedRelativeFrobenius (p := p) f n).left
  inv := iteratedRelativeFrobeniusLeftInv (p := p) f n
  hom_inv_id := sorry
  inv_hom_id := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]

/-- The underlying scheme of an étale object over a scheme of characteristic `p`
again has characteristic `p`. -/
instance instIsCharP_etale (X : SchemeOverField k) (U : X.left.Etale) :
    Scheme.IsCharP ((Functor.fromPUnit (Over.left X)).obj U.right) p :=
  instIsCharP X

/-- The small-étale site isomorphism `U ≅ U ×_{π_X} X` induced by iterated
relative Frobenius of an étale morphism `U ⟶ X`. -/
def geometricFrobenius_smallEtalePullbackIso (X : SchemeOverField k) :
    𝟭 X.left.Etale ≅ smallEtalePullback (geometricFrobenius_ofFiniteField X) :=
  NatIso.ofComponents
    (fun U ↦
      -- Local instance justification (search instability): `U.hom` has target `X.left`, but instance search sees the Over-comma `fromPUnit` unfolding.
      letI : Scheme.IsCharP ((Functor.fromPUnit (Over.left X)).obj U.right) p :=
        instIsCharP X
      -- Local instance justification (search instability): `U.prop` is `Etale U.hom`, but the étale-site instance does not fire on `X.left.Etale` objects.
      letI : Etale U.hom := U.prop
      MorphismProperty.Over.isoMk
        (iteratedRelativeFrobeniusLeftIso (p := p) U.hom (finiteFieldRank k p))
        sorry)
    (fun {_ _} _ ↦ sorry)

/-- The component `γ_U : U ⟶ U ×_{U.hom, X, π_X} X` of the small-étale site
isomorphism of geometric Frobenius. -/
def geometricFrobenius_smallEtalePullbackIso_hom_app (X : SchemeOverField k)
    (U : X.left.Etale) :
    U ⟶ (smallEtalePullback (geometricFrobenius_ofFiniteField X)).obj U :=
  (geometricFrobenius_smallEtalePullbackIso X).hom.app U

/-- The first projection of `γ_U` is the `finiteFieldRank`-fold absolute
Frobenius of `U`. -/
theorem geometricFrobenius_smallEtalePullbackIso_hom_app_fst
    (X : SchemeOverField k) (U : X.left.Etale) :
    (geometricFrobenius_smallEtalePullbackIso_hom_app X U).left ≫
        pullback.fst U.hom (geometricFrobenius_ofFiniteField X) =
      Hom.absoluteFrobeniusPowSource (p := p) U.hom (finiteFieldRank k p) :=
  sorry

/-- The second projection of `γ_U` is the structure morphism `U ⟶ X`. -/
theorem geometricFrobenius_smallEtalePullbackIso_hom_app_snd
    (X : SchemeOverField k) (U : X.left.Etale) :
    (geometricFrobenius_smallEtalePullbackIso_hom_app X U).left ≫
        pullback.snd U.hom (geometricFrobenius_ofFiniteField X) =
      U.hom :=
  sorry

/-- Canonical identification `π_X⁻¹ F ≅ F` of abelian sheaves on `X`, induced
by the small-étale site isomorphism of geometric Frobenius. -/
def geometricFrobeniusSheafIso (X : SchemeOverField k) :
    etaleAbelianSheafPullback (geometricFrobenius_ofFiniteField X) ≅
      𝟭 (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :=
  etaleAbelianSheafPullbackIso (geometricFrobenius_smallEtalePullbackIso X)

/-- The component of `geometricFrobeniusSheafIso` at an abelian sheaf. -/
def geometricFrobeniusSheafIso_hom_app (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback (geometricFrobenius_ofFiniteField X)).obj F ⟶ F :=
  (geometricFrobeniusSheafIso X).hom.app F

/-- `geometricFrobeniusSheafIso` is the transport of the small-étale site
isomorphism of geometric Frobenius along `etaleAbelianSheafPullbackIso`. -/
theorem geometricFrobeniusSheafIso_spec (X : SchemeOverField k) :
    geometricFrobeniusSheafIso X =
      etaleAbelianSheafPullbackIso (geometricFrobenius_smallEtalePullbackIso X) :=
  sorry

/-- Canonical identification `F ≅ (π_X)_* F` of abelian sheaves on `X`, induced
by the small-étale site isomorphism of geometric Frobenius. -/
def geometricFrobeniusSheafPushforwardIso (X : SchemeOverField k) :
    𝟭 (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) ≅
      (smallEtalePullback (geometricFrobenius_ofFiniteField X)).sheafPushforwardContinuous
        AddCommGrpCat.{u} X.left.smallEtaleTopology X.left.smallEtaleTopology :=
  (Functor.sheafPushforwardContinuousId'
      (geometricFrobenius_smallEtalePullbackIso X).symm
      AddCommGrpCat.{u} X.left.smallEtaleTopology).symm

/-- The component of `geometricFrobeniusSheafPushforwardIso` at an abelian
sheaf. -/
def geometricFrobeniusSheafPushforwardIso_hom_app (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    F ⟶
      ((smallEtalePullback (geometricFrobenius_ofFiniteField X)).sheafPushforwardContinuous
          AddCommGrpCat.{u} X.left.smallEtaleTopology
          X.left.smallEtaleTopology).obj F :=
  (geometricFrobeniusSheafPushforwardIso X).hom.app F

/-- `geometricFrobeniusSheafPushforwardIso` is the inverse of
`sheafPushforwardContinuousId'` applied to the inverse small-étale site
isomorphism of geometric Frobenius. -/
theorem geometricFrobeniusSheafPushforwardIso_spec (X : SchemeOverField k) :
    geometricFrobeniusSheafPushforwardIso X =
      (Functor.sheafPushforwardContinuousId'
          (geometricFrobenius_smallEtalePullbackIso X).symm
          AddCommGrpCat.{u} X.left.smallEtaleTopology).symm :=
  sorry

/-- On sections over an étale `U`, the isomorphism `F ≅ (π_X)_* F` is restriction
along `γ_U⁻¹`. -/
theorem geometricFrobeniusSheafPushforwardIso_hom_app_app
    (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (U : X.left.Etale) :
    ((geometricFrobeniusSheafPushforwardIso X).hom.app F).hom.app (Opposite.op U) =
      F.obj.map
        ((geometricFrobenius_smallEtalePullbackIso X).inv.app U).op :=
  sorry

end AlgebraicGeometry.SchemeOverField
