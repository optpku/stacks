module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Data.ZMod.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.Adjunction.ExactFunctor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Adjunction.Derived
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section
variable {A B : Scheme.{u}} (p : A ⟶ B) (n : ℕ)
variable [HasSheafify A.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
variable [HasSheafify B.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
variable [((smallEtalePullback p).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
    B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]

/-- Direct image of small-étale sheaves of `ZMod n`-modules along a morphism of schemes. -/
noncomputable abbrev zmodSheafPushforward :
    Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n)) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n)) :=
  (smallEtalePullback p).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
    B.smallEtaleTopology A.smallEtaleTopology

/-- Inverse image of small-étale sheaves of `ZMod n`-modules along a morphism of schemes. -/
noncomputable abbrev zmodSheafPullback :
    Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n)) ⥤
      Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n)) :=
  (smallEtalePullback p).sheafPullback (ModuleCat.{u} (ZMod n))
    B.smallEtaleTopology A.smallEtaleTopology

/-- Underived adjunction `p⁻¹ ⊣ p_*` on small-étale sheaves of `ZMod n`-modules. -/
noncomputable abbrev zmodSheafAdjunction :
    zmodSheafPullback p n ⊣ zmodSheafPushforward p n :=
  (smallEtalePullback p).sheafAdjunctionContinuous (ModuleCat.{u} (ZMod n))
    B.smallEtaleTopology A.smallEtaleTopology

/-- `zmodSheafPushforward` is continuous sheaf pushforward along `smallEtalePullback`. -/
theorem zmodSheafPushforward_eq :
    zmodSheafPushforward p n =
      (smallEtalePullback p).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology A.smallEtaleTopology := sorry

/-- `zmodSheafPullback` is sheaf pullback along `smallEtalePullback`. -/
theorem zmodSheafPullback_eq :
    zmodSheafPullback p n =
      (smallEtalePullback p).sheafPullback (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology A.smallEtaleTopology := sorry

/-- `zmodSheafAdjunction` is the continuous sheaf adjunction along `smallEtalePullback`. -/
theorem zmodSheafAdjunction_eq :
    zmodSheafAdjunction p n =
      (smallEtalePullback p).sheafAdjunctionContinuous (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology A.smallEtaleTopology := sorry

variable [PreservesFiniteLimits (zmodSheafPullback p n)]
variable [(zmodSheafPullback p n).Additive]
variable [(zmodSheafPushforward p n).Additive]

/-- Exact inverse image of small-étale sheaves of `ZMod n`-modules. -/
noncomputable abbrev zmodPullbackExact :
    Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n)) ⥤ₑ
      Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n)) :=
  Adjunction.exactLeftAdjoint (zmodSheafAdjunction p n)

/-- `zmodPullbackExact` is the exact left adjoint of `zmodSheafAdjunction`. -/
theorem zmodPullbackExact_eq :
    zmodPullbackExact p n =
      Adjunction.exactLeftAdjoint (zmodSheafAdjunction p n) := sorry

variable [HasDerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]

/-- Derived inverse image `p⁻¹` on `D(-_étale, ZMod n)`. -/
noncomputable abbrev zmodDerivedInverseImage :
    DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))) ⥤
      DerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n))) :=
  KInjective.left (zmodPullbackExact p n)

/-- `zmodDerivedInverseImage` is the K-injective exact left action of inverse image. -/
theorem zmodDerivedInverseImage_eq :
    zmodDerivedInverseImage p n = KInjective.left (zmodPullbackExact p n) := sorry

variable [IsGrothendieckAbelian (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]

/-- Derived pushforward `Rp_*` on `D(-_étale, ZMod n)`. -/
noncomputable abbrev zmodDerivedPushforward :
    DerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n))) ⥤
      DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))) :=
  KInjective.right (zmodSheafPushforward p n)

/-- `zmodDerivedPushforward` is the K-injective total right-derived functor of pushforward. -/
theorem zmodDerivedPushforward_eq :
    zmodDerivedPushforward p n = KInjective.right (zmodSheafPushforward p n) := sorry

end

/-- Small étale sites of schemes admit sheafification of `ZMod n`-modules. -/
instance instHasSheafify_smallEtaleZMod {X : Scheme.{u}} {n : ℕ} :
    HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n)) :=
  sorry

/-- Small-étale sheaves of `ZMod n`-modules form a Grothendieck abelian category. -/
instance instIsGrothendieckAbelian_smallEtaleZMod {X : Scheme.{u}} {n : ℕ} :
    IsGrothendieckAbelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))) :=
  sorry

/-- Continuous sheaf pushforward of `ZMod n`-modules along small-étale pullback is a right adjoint. -/
instance isRightAdjoint_zmodSheafPushforward {A B : Scheme.{u}} {p : A ⟶ B} {n : ℕ} :
    ((smallEtalePullback p).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint := sorry

/-- Continuous direct image of small-étale `ZMod n`-module sheaves is additive. -/
instance additive_zmodSheafPushforward {A B : Scheme.{u}} {p : A ⟶ B} {n : ℕ}
    [HasSheafify A.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify B.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [((smallEtalePullback p).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint] :
    (zmodSheafPushforward p n).Additive := sorry

/-- Inverse image of small-étale `ZMod n`-module sheaves is additive. -/
instance additive_zmodSheafPullback {A B : Scheme.{u}} {p : A ⟶ B} {n : ℕ}
    [HasSheafify A.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify B.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [((smallEtalePullback p).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint] :
    (zmodSheafPullback p n).Additive := sorry

/-- Inverse image of small-étale `ZMod n`-module sheaves preserves finite limits. -/
instance preservesFiniteLimits_zmodSheafPullback {A B : Scheme.{u}} {p : A ⟶ B} {n : ℕ}
    [HasSheafify A.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify B.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [((smallEtalePullback p).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint] :
    PreservesFiniteLimits (zmodSheafPullback p n) := sorry


/-- Pullback of small-étale `ZMod n`-module sheaves along a composite is the composite pullback. -/
noncomputable def zmodSheafPullback_comp {A B C : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (n : ℕ)
    [HasSheafify A.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify B.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify C.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [((smallEtalePullback p).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        A.smallEtaleTopology B.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback q).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology C.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (q ≫ p)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        A.smallEtaleTopology C.smallEtaleTopology).IsRightAdjoint] :
    zmodSheafPullback p n ⋙ zmodSheafPullback q n ≅
      zmodSheafPullback (q ≫ p) n :=
  let siteIso :
      smallEtalePullback p ⋙ smallEtalePullback q ≅ smallEtalePullback (q ≫ p) :=
    (MorphismProperty.Over.pullbackComp q p).symm
  -- Local instance justification (search instability): pin continuity of p's site pullback for sheafPushforwardContinuousComp'.
  letI := smallEtalePullback_isContinuous p
  -- Local instance justification (search instability): pin continuity of q's site pullback for sheafPushforwardContinuousComp'.
  letI := smallEtalePullback_isContinuous q
  -- Local instance justification (search instability): pin continuity of the composite's site pullback for sheafPushforwardContinuousComp'.
  letI := smallEtalePullback_isContinuous (q ≫ p)
  Adjunction.leftAdjointCompIso
    (zmodSheafAdjunction p n) (zmodSheafAdjunction q n)
    (zmodSheafAdjunction (q ≫ p) n)
    (Functor.sheafPushforwardContinuousComp' siteIso (ModuleCat.{u} (ZMod n))
      A.smallEtaleTopology B.smallEtaleTopology C.smallEtaleTopology)

/-- Inverse-image identification along equal morphisms, by substitution of the morphism equality. -/
noncomputable def zmodSheafPullback_congr {A B : Scheme.{u}} {p q : A ⟶ B}
    (h : p = q) (n : ℕ)
    [HasSheafify A.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify B.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [((smallEtalePullback p).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback q).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint] :
    zmodSheafPullback p n ≅ zmodSheafPullback q n :=
  eqToIso (congrArg (fun r : A ⟶ B ↦ zmodSheafPullback r n) h)

/-- The left-adjoint square of étale `ZMod n` inverse images of a cartesian square of schemes. -/
noncomputable def zmodSheafPullback_square
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint] :
    zmodSheafPullback g n ⋙ zmodSheafPullback f' n ≅
      zmodSheafPullback f n ⋙ zmodSheafPullback g' n :=
  zmodSheafPullback_comp g f' n ≪≫
    zmodSheafPullback_congr h_cart.w.symm n ≪≫
    (zmodSheafPullback_comp f g' n).symm

/-- `zmodSheafPullback_square` is the composite of the two path identifications. -/
theorem zmodSheafPullback_square_eq
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint] :
    zmodSheafPullback_square f g f' g' h_cart n =
      zmodSheafPullback_comp g f' n ≪≫
        zmodSheafPullback_congr h_cart.w.symm n ≪≫
        (zmodSheafPullback_comp f g' n).symm := sorry

/-- Bundled exact-functor form of the inverse-image square of a cartesian scheme square. -/
noncomputable def zmodPullbackExact_square
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint] :
    (zmodPullbackExact g n).comp (zmodPullbackExact f' n) ≅
      (zmodPullbackExact f n).comp (zmodPullbackExact g' n) :=
  (exactFunctor
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))).isoMk
    (zmodSheafPullback_square f g f' g' h_cart n)

/-- Derived inverse-image square `g⁻¹ ⋙ (f')⁻¹ ≅ f⁻¹ ⋙ (g')⁻¹` on `D(-_étale, ZMod n)`. -/
noncomputable def zmodDerivedPullbackSquare
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint] :
    zmodDerivedInverseImage g n ⋙ zmodDerivedInverseImage f' n ≅
      zmodDerivedInverseImage f n ⋙ zmodDerivedInverseImage g' n :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (zmodPullbackExact g n) (zmodPullbackExact f' n)).symm ≪≫
    ExactFunctor.MapDerivedCategory.mapIso
      (zmodPullbackExact_square f g f' g' h_cart n) ≪≫
    ExactFunctor.MapDerivedCategory.compFunctorIso
      (zmodPullbackExact f n) (zmodPullbackExact g' n)

/-- `zmodDerivedPullbackSquare` is the derived image of the underived inverse-image square. -/
theorem zmodDerivedPullbackSquare_eq
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint] :
    zmodDerivedPullbackSquare f g f' g' h_cart n =
      (ExactFunctor.MapDerivedCategory.compFunctorIso
          (zmodPullbackExact g n) (zmodPullbackExact f' n)).symm ≪≫
        ExactFunctor.MapDerivedCategory.mapIso
          (zmodPullbackExact_square f g f' g' h_cart n) ≪≫
        ExactFunctor.MapDerivedCategory.compFunctorIso
          (zmodPullbackExact f n) (zmodPullbackExact g' n) := sorry

/-- Derived base-change transformation `g⁻¹ Rf_* ⟶ Rf'_* (g')⁻¹` on `D(-_étale, ZMod n)`. -/
noncomputable def zmodDerivedBaseChange
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint] :
    zmodDerivedPushforward f n ⋙ zmodDerivedInverseImage g n ⟶
      zmodDerivedInverseImage g' n ⋙ zmodDerivedPushforward f' n :=
  DerivedBaseChange.map
    (KInjective.adjunction (zmodPullbackExact f n)
      (zmodSheafPushforward f n) (zmodSheafAdjunction f n))
    (KInjective.adjunction (zmodPullbackExact f' n)
      (zmodSheafPushforward f' n) (zmodSheafAdjunction f' n))
    (zmodDerivedPullbackSquare f g f' g' h_cart n)

/-- `zmodDerivedBaseChange` is `DerivedBaseChange.map` of the two K-injective adjunctions. -/
theorem zmodDerivedBaseChange_eq
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint] :
    zmodDerivedBaseChange f g f' g' h_cart n =
      DerivedBaseChange.map
        (KInjective.adjunction (zmodPullbackExact f n)
          (zmodSheafPushforward f n) (zmodSheafAdjunction f n))
        (KInjective.adjunction (zmodPullbackExact f' n)
          (zmodSheafPushforward f' n) (zmodSheafAdjunction f' n))
        (zmodDerivedPullbackSquare f g f' g' h_cart n) := sorry

/-- Component `g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` of the derived étale `ZMod n` base-change map. -/
noncomputable def zmodDerivedBaseChangeHom
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    (zmodDerivedInverseImage g n).obj ((zmodDerivedPushforward f n).obj E) ⟶
      (zmodDerivedPushforward f' n).obj ((zmodDerivedInverseImage g' n).obj E) :=
  (zmodDerivedBaseChange f g f' g' h_cart n).app E

/-- `zmodDerivedBaseChangeHom` is the component of `zmodDerivedBaseChange`. -/
theorem zmodDerivedBaseChangeHom_eq
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    zmodDerivedBaseChangeHom f g f' g' h_cart n E =
      (zmodDerivedBaseChange f g f' g' h_cart n).app E := sorry

/-- The named component satisfies the `DerivedBaseChange.IsMapAt` mate equation. -/
theorem zmodDerivedBaseChangeHom_isMapAt
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (n : ℕ)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [IsGrothendieckAbelian (Sheaf X'.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback f').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y'.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback g').sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        X.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (f' ≫ g)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (g' ≫ f)).sheafPushforwardContinuous (ModuleCat.{u} (ZMod n))
        Y.smallEtaleTopology X'.smallEtaleTopology).IsRightAdjoint]
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))) :
    DerivedBaseChange.IsMapAt
      (KInjective.adjunction (zmodPullbackExact f n)
        (zmodSheafPushforward f n) (zmodSheafAdjunction f n))
      (KInjective.adjunction (zmodPullbackExact f' n)
        (zmodSheafPushforward f' n) (zmodSheafAdjunction f' n))
      (zmodDerivedPullbackSquare f g f' g' h_cart n) E
      (zmodDerivedBaseChangeHom f g f' g' h_cart n E) := sorry


end AlgebraicGeometry.Scheme.Etale

end

end
