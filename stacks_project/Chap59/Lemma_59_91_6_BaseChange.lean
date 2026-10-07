module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import stacks_project.Chap59.Lemma_59_51_7_HigherDirectImage
public import stacks_project.Chap59.Lemma_59_67_3_Torsion
public import stacks_project.Chap59.Lemma_59_80_9_Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}
variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]

/-- Inverse image of an abelian small-étale sheaf along a morphism of schemes. -/
noncomputable abbrev abelianPullbackAlong {A B : Scheme.{u}} (h : A ⟶ B)
    (G : Sheaf B.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf A.smallEtaleTopology AddCommGrpCat.{u} :=
  (etaleAbelianSheafPullback h).obj G

/-- Direct image of an abelian small-étale sheaf along a morphism of schemes. -/
noncomputable abbrev abelianPushforwardAlong {A B : Scheme.{u}} (h : A ⟶ B) :
    Sheaf A.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf B.smallEtaleTopology AddCommGrpCat.{u} :=
  (smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
    B.smallEtaleTopology A.smallEtaleTopology

/-- `abelianPushforwardAlong` is sheaf pushforward along `smallEtalePullback`. -/
theorem abelianPushforwardAlong_eq {A B : Scheme.{u}} (h : A ⟶ B) :
    abelianPushforwardAlong h =
      (smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
        B.smallEtaleTopology A.smallEtaleTopology := sorry

/-- Pullback of abelian small-étale sheaves along a composite is the composite pullback. -/
noncomputable def etaleAbelianSheafPullback_comp {A B C : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) :
    etaleAbelianSheafPullback p ⋙ etaleAbelianSheafPullback q ≅
      etaleAbelianSheafPullback (q ≫ p) :=
  let siteIso :
      smallEtalePullback p ⋙ smallEtalePullback q ≅ smallEtalePullback (q ≫ p) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) q p).symm
  Adjunction.leftAdjointCompIso
    ((smallEtalePullback p).sheafAdjunctionContinuous AddCommGrpCat.{u}
      A.smallEtaleTopology B.smallEtaleTopology)
    ((smallEtalePullback q).sheafAdjunctionContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology C.smallEtaleTopology)
    ((smallEtalePullback (q ≫ p)).sheafAdjunctionContinuous AddCommGrpCat.{u}
      A.smallEtaleTopology C.smallEtaleTopology)
    (Functor.sheafPushforwardContinuousComp' siteIso AddCommGrpCat.{u}
      A.smallEtaleTopology B.smallEtaleTopology C.smallEtaleTopology)

/-- The left-adjoint square of étale inverse images associated to a cartesian square of schemes. -/
noncomputable def etaleAbelianSheafPullback_square
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) :
    etaleAbelianSheafPullback g ⋙ etaleAbelianSheafPullback f' ≅
      etaleAbelianSheafPullback f ⋙ etaleAbelianSheafPullback g' :=
  etaleAbelianSheafPullback_comp (A := Y) (B := Y') (C := X') g f' ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ etaleAbelianSheafPullback h) h_cart.w.symm) ≪≫
    (etaleAbelianSheafPullback_comp (A := Y) (B := X) (C := X') f g').symm

/-- Underived base-change mate `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of a cartesian square. -/
noncomputable def underivedBaseChange
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) :
    abelianPushforwardAlong f ⋙ etaleAbelianSheafPullback g ⟶
      etaleAbelianSheafPullback g' ⋙ abelianPushforwardAlong f' :=
  DerivedBaseChange.map
    ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology)
    ((smallEtalePullback f').sheafAdjunctionContinuous AddCommGrpCat.{u}
      Y'.smallEtaleTopology X'.smallEtaleTopology)
    (etaleAbelianSheafPullback_square f g f' g' h_cart)

/-- `underivedBaseChange` is the right mate of the inverse-image square. -/
theorem underivedBaseChange_eq
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) :
    underivedBaseChange f g f' g' h_cart =
      DerivedBaseChange.map
        ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u}
          Y.smallEtaleTopology X.smallEtaleTopology)
        ((smallEtalePullback f').sheafAdjunctionContinuous AddCommGrpCat.{u}
          Y'.smallEtaleTopology X'.smallEtaleTopology)
        (etaleAbelianSheafPullback_square f g f' g' h_cart) := sorry

/-- Degree-`q` sheaf comparison `g⁻¹ R^q f_* F ⟶ R^q f'_* (g')⁻¹ F`, obtained by
right-deriving the underived mate. -/
noncomputable def higherDirectImage_baseChangeHom
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) :
    ((abelianPushforwardAlong f ⋙ etaleAbelianSheafPullback g).rightDerived q).obj F ⟶
      ((etaleAbelianSheafPullback g' ⋙ abelianPushforwardAlong f').rightDerived q).obj F :=
  (NatTrans.rightDerived (underivedBaseChange f g f' g' h_cart) q).app F


/-- `higherDirectImage_baseChangeHom` is the degree-`q` right derived component of the
underived mate. -/
theorem higherDirectImage_baseChangeHom_eq
    (f : X ⟶ Y) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) :
    higherDirectImage_baseChangeHom f g f' g' h_cart F q =
      (NatTrans.rightDerived (underivedBaseChange f g f' g' h_cart) q).app F := sorry

/-- Cohomology commutes with base change for `f` when the canonical degree-`q`
comparisons of a cartesian square are isomorphisms for every torsion abelian
étale sheaf. -/
def CohomologyCommutesWithBaseChange (f : X ⟶ Y) : Prop :=
  ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
      IsLocallyTorsion F →
      ∀ q : ℕ, IsIso (higherDirectImage_baseChangeHom f g f' g' h_cart F q)

/-- Unpacking: the named degree-`q` comparison of a cartesian square is an isomorphism. -/
theorem cohomologyCommutesWithBaseChange_apply {f : X ⟶ Y}
    (h : CohomologyCommutesWithBaseChange f)
    {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (h_cart : IsPullback g' f' f g)
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (hF : IsLocallyTorsion F)
    (q : ℕ) :
    IsIso (higherDirectImage_baseChangeHom f g f' g' h_cart F q) := sorry

/-- Vanishing of positive higher direct images of inverse images of injective
`ℤ/ℓℤ`-module sheaves after arbitrary base change of `f`. -/
def injectiveMod_higherDirectImage_isZero (f : X ⟶ Y) : Prop :=
  ∀ (ℓ : ℕ), Nat.Prime ℓ →
    ∀ (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
      Injective I → IsLocallyEllTorsion ℓ I →
      ∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X),
        IsPullback g' f' f g →
        ∀ q : ℕ, 0 < q →
          IsZero (schemeHigherDirectImage f' (abelianPullbackAlong g' I) q)

/-- Unpacking: `R^q f'_* (g')⁻¹ I` vanishes for `q > 0` when `I` is injective
and locally `ℓ`-torsion. -/
theorem injectiveMod_higherDirectImage_isZero_apply {f : X ⟶ Y}
    (h : injectiveMod_higherDirectImage_isZero f)
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ)
    {I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (hI : Injective I) (hℓI : IsLocallyEllTorsion ℓ I)
    {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (h_cart : IsPullback g' f' f g) {q : ℕ} (hq : 0 < q) :
    IsZero (schemeHigherDirectImage f' (abelianPullbackAlong g' I) q) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
