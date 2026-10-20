module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Data.ZMod.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.Adjunction.ExactFunctor

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
        B.smallEtaleTopology A.smallEtaleTopology := rfl

/-- `zmodSheafPullback` is sheaf pullback along `smallEtalePullback`. -/
theorem zmodSheafPullback_eq :
    zmodSheafPullback p n =
      (smallEtalePullback p).sheafPullback (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology A.smallEtaleTopology := rfl

/-- `zmodSheafAdjunction` is the continuous sheaf adjunction along `smallEtalePullback`. -/
theorem zmodSheafAdjunction_eq :
    zmodSheafAdjunction p n =
      (smallEtalePullback p).sheafAdjunctionContinuous (ModuleCat.{u} (ZMod n))
        B.smallEtaleTopology A.smallEtaleTopology := rfl

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
      Adjunction.exactLeftAdjoint (zmodSheafAdjunction p n) := rfl

variable [HasDerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
variable [HasDerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]

/-- Derived inverse image `p⁻¹` on `D(-_étale, ZMod n)`. -/
noncomputable abbrev zmodDerivedInverseImage :
    DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))) ⥤
      DerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n))) :=
  KInjective.left (zmodPullbackExact p n)

/-- `zmodDerivedInverseImage` is the K-injective exact left action of inverse image. -/
theorem zmodDerivedInverseImage_eq :
    zmodDerivedInverseImage p n = KInjective.left (zmodPullbackExact p n) := rfl

variable [IsGrothendieckAbelian (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]

/-- Derived pushforward `Rp_*` on `D(-_étale, ZMod n)`. -/
noncomputable abbrev zmodDerivedPushforward :
    DerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n))) ⥤
      DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n))) :=
  KInjective.right (zmodSheafPushforward p n)

/-- `zmodDerivedPushforward` is the K-injective total right-derived functor of pushforward. -/
theorem zmodDerivedPushforward_eq :
    zmodDerivedPushforward p n = KInjective.right (zmodSheafPushforward p n) := rfl

end

/-- Small étale sites of schemes have sheafification of `ZMod n`-modules. -/
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

end AlgebraicGeometry.Scheme.Etale

end

end
