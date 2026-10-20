module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.IteratedRelative.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.FiniteField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.PullbackIso

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u v w

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]

/-- Geometric Frobenius of `X / k` agrees with the `finiteFieldRank`-fold absolute
Frobenius of the underlying scheme. -/
theorem geometricFrobenius_ofFiniteField_eq_absoluteFrobeniusPow
    (X : SchemeOverField k) :
    geometricFrobenius_ofFiniteField X =
      absoluteFrobeniusPow p X.left (finiteFieldRank k p) :=
  sorry

/-- The iterated relative Frobenius component commutes with projection to the base. -/
theorem geometricFrobenius_smallEtalePullbackIso_component_over
    (X : SchemeOverField k) (U : X.left.Etale) :
    (@iteratedRelativeFrobeniusLeftIso p ‹Fact p.Prime› U.left X.left U.hom
        (instIsCharP X) U.prop (finiteFieldRank k p)).hom ≫
        ((smallEtalePullback (geometricFrobenius_ofFiniteField X)).obj U).hom =
      U.hom := sorry

/-- The iterated relative Frobenius identifies an étale object with its geometric
Frobenius pullback. -/
def geometricFrobenius_smallEtalePullbackIso_component
    (X : SchemeOverField k) (U : X.left.Etale) :
    U ≅ (smallEtalePullback (geometricFrobenius_ofFiniteField X)).obj U :=
  MorphismProperty.Over.isoMk
    (@iteratedRelativeFrobeniusLeftIso p ‹Fact p.Prime› U.left X.left U.hom
      (instIsCharP X) U.prop (finiteFieldRank k p))
    (geometricFrobenius_smallEtalePullbackIso_component_over X U)

/-- The iterated relative Frobenius components are natural in étale objects. -/
theorem geometricFrobenius_smallEtalePullbackIso_naturality
    (X : SchemeOverField k) {U V : X.left.Etale} (f : U ⟶ V) :
    f ≫ (geometricFrobenius_smallEtalePullbackIso_component X V).hom =
      (geometricFrobenius_smallEtalePullbackIso_component X U).hom ≫
        (smallEtalePullback (geometricFrobenius_ofFiniteField X)).map f := sorry

/-- The small-étale site isomorphism induced by iterated relative Frobenius. -/
def geometricFrobenius_smallEtalePullbackIso (X : SchemeOverField k) :
    𝟭 X.left.Etale ≅ smallEtalePullback (geometricFrobenius_ofFiniteField X) :=
  NatIso.ofComponents
    (geometricFrobenius_smallEtalePullbackIso_component X)
    (geometricFrobenius_smallEtalePullbackIso_naturality X)

/-- The first projection of the geometric Frobenius site comparison is the
`finiteFieldRank`-fold absolute Frobenius of the étale object. -/
theorem geometricFrobenius_smallEtalePullbackIso_hom_app_fst
    (X : SchemeOverField k) (U : X.left.Etale) :
    ((geometricFrobenius_smallEtalePullbackIso X).hom.app U).left ≫
        pullback.fst U.hom (geometricFrobenius_ofFiniteField X) =
      Hom.absoluteFrobeniusPowSource (p := p) (S := X.left) U.hom (finiteFieldRank k p) :=
  sorry

/-- Direct image along geometric Frobenius is canonically isomorphic to the
identity on étale sheaves with values in any coefficient category. -/
def geometricFrobeniusSheafPushforwardIso (X : SchemeOverField k)
    (A : Type v) [Category.{w} A] :
    𝟭 (Sheaf X.left.smallEtaleTopology A) ≅
      (smallEtalePullback (geometricFrobenius_ofFiniteField X)).sheafPushforwardContinuous
        A X.left.smallEtaleTopology X.left.smallEtaleTopology :=
  (Functor.sheafPushforwardContinuousId'
      (geometricFrobenius_smallEtalePullbackIso X).symm
      A X.left.smallEtaleTopology).symm

/-- Geometric Frobenius direct image on étale sheaves is a right adjoint,
via its canonical identification with the identity functor. -/
instance instIsRightAdjoint_geometricFrobeniusSheafPushforward
    (X : SchemeOverField k) (A : Type v) [Category.{w} A] :
    ((smallEtalePullback (geometricFrobenius_ofFiniteField X)).sheafPushforwardContinuous
      A X.left.smallEtaleTopology X.left.smallEtaleTopology).IsRightAdjoint :=
  (Adjunction.id.ofNatIsoRight (geometricFrobeniusSheafPushforwardIso X A)).isRightAdjoint

/-- Inverse image along geometric Frobenius is canonically isomorphic to the
identity on étale sheaves with values in any coefficient category. -/
def geometricFrobeniusSheafPullbackIso (X : SchemeOverField k)
    (A : Type v) [Category.{w} A] :
    (smallEtalePullback (geometricFrobenius_ofFiniteField X)).sheafPullback
        A X.left.smallEtaleTopology X.left.smallEtaleTopology ≅
      𝟭 (Sheaf X.left.smallEtaleTopology A) :=
  Adjunction.leftAdjointUniq
    ((smallEtalePullback (geometricFrobenius_ofFiniteField X)).sheafAdjunctionContinuous
      A X.left.smallEtaleTopology X.left.smallEtaleTopology)
    (Adjunction.id.ofNatIsoRight (geometricFrobeniusSheafPushforwardIso X A))

/-- On sections over an étale object, the forward geometric Frobenius direct-image
comparison is restriction along the inverse of the site comparison. -/
theorem geometricFrobeniusSheafPushforwardIso_hom_app_app
    (X : SchemeOverField k) (A : Type v) [Category.{w} A]
    (F : Sheaf X.left.smallEtaleTopology A) (U : X.left.Etale) :
    ((geometricFrobeniusSheafPushforwardIso X A).hom.app F).hom.app (Opposite.op U) =
      F.obj.map ((geometricFrobenius_smallEtalePullbackIso X).inv.app U).op :=
  sorry

/-- Canonical identification `π_X^{-1} F ≅ F` of abelian sheaves on `X`, induced
by the small-étale site isomorphism of geometric Frobenius. -/
def geometricFrobeniusSheafIso (X : SchemeOverField k) :
    etaleAbelianSheafPullback (geometricFrobenius_ofFiniteField X) ≅
      𝟭 (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :=
  etaleAbelianSheafPullbackIso (geometricFrobenius_smallEtalePullbackIso X)

/-- The canonical morphism from geometric Frobenius inverse image of an abelian
étale sheaf to the original sheaf. -/
def geometricFrobeniusSheafIso_hom_app (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback (geometricFrobenius_ofFiniteField X)).obj F ⟶ F :=
  (geometricFrobeniusSheafIso X).hom.app F

end AlgebraicGeometry.SchemeOverField
