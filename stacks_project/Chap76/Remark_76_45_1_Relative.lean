/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.AffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_4_2_Pullback

/-!
# Representable matching for relative pseudo-coherence

A locally finite type morphism of representable algebraic spaces over a scheme `S`
is represented by a morphism of schemes `f0 : X0 ⟶ Y0`. An object of
`D_QCoh(𝒪_{ofOver X0})` is the étale identification of `ε* E0` for a unique
`E0` in `D_QCoh(𝒪_{X0})`, and relative `m`-pseudo-coherence is the Section 37.59
affine-cover criterion on that `E0`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme.DerivedQCoh (SmallEtale epsilonStar)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of representable algebraic spaces over `S` is locally of finite type if
and only if the representing morphism of schemes is locally of finite type. -/
theorem locallyOfFiniteType_ofOverMap_iff {S : Scheme.{u}} {X0 Y0 : Over S}
    (f0 : X0 ⟶ Y0) :
    LocallyOfFiniteType (ofOverMap f0) ↔
      AlgebraicGeometry.LocallyOfFiniteType f0.left :=
  sorry

/-- Local finite type of `ofOverMap f0` yields local finite type of the underlying
scheme morphism `f0.left`. -/
instance instLocallyOfFiniteType_left_ofOverMap {S : Scheme.{u}} {X0 Y0 : Over S}
    (f0 : X0 ⟶ Y0) [LocallyOfFiniteType (ofOverMap f0)] :
    AlgebraicGeometry.LocallyOfFiniteType f0.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Direct image along `schemeEtaleRingedHom U` preserves finite limits. -/
instance schemeEtaleRingedHom_modulePushforward_preservesFiniteLimits
    {S : Scheme.{u}} (U : Over S) :
    PreservesFiniteLimits (schemeEtaleRingedHom U).modulePushforward.{u} :=
  sorry

/-- Direct image along `schemeEtaleRingedHom U` preserves finite colimits. -/
instance schemeEtaleRingedHom_modulePushforward_preservesFiniteColimits
    {S : Scheme.{u}} (U : Over S) :
    PreservesFiniteColimits (schemeEtaleRingedHom U).modulePushforward.{u} :=
  sorry

/-- `E` on `ofOver U` is the pullback of `E0` after identifying the small étale site of
`ofOver U` with that of `U.left` via `schemeEtaleRingedHom`, then applying `ε*` from
Lemma 75.4.2. -/
def isEpsilonStarPullback {S : Scheme.{u}} (U : Over S)
    (E : ModuleDerived (ofOver U)) (E0 : Scheme.DerivedQCoh U.left) : Prop :=
  IsIsomorphic
    (((schemeEtaleRingedHom U).modulePushforward.{u}).mapDerivedCategory.obj E)
    ((Scheme.DerivedQCoh.SmallEtale.inclusion U.left).obj
      ((Scheme.DerivedQCoh.epsilonStar U.left).obj E0))

/-- The étale/`ε*` comparison unfolds to an isomorphism after `schemeEtaleRingedHom`
and Lemma 75.4.2. -/
theorem isEpsilonStarPullback_iff {S : Scheme.{u}} (U : Over S)
    (E : ModuleDerived (ofOver U)) (E0 : Scheme.DerivedQCoh U.left) :
    isEpsilonStarPullback U E E0 ↔
      IsIsomorphic
        (((schemeEtaleRingedHom U).modulePushforward.{u}).mapDerivedCategory.obj E)
        ((Scheme.DerivedQCoh.SmallEtale.inclusion U.left).obj
          ((Scheme.DerivedQCoh.epsilonStar U.left).obj E0)) :=
  sorry

/-- Comparison isomorphism identifying the `schemeEtaleRingedHom` pushforward of `E` with
`ε* E0` on the small étale site of `U.left`. -/
abbrev EpsilonStarComparisonIso {S : Scheme.{u}} (U : Over S)
    (E : ModuleDerived (ofOver U)) (E0 : Scheme.DerivedQCoh U.left) :=
  ((schemeEtaleRingedHom U).modulePushforward.{u}).mapDerivedCategory.obj E ≅
    (SmallEtale.inclusion U.left).obj ((epsilonStar U.left).obj E0)

/-- An étale/`ε*` comparison exists if and only if the corresponding comparison isomorphism
type is inhabited. -/
theorem nonempty_epsilonStarComparisonIso_iff {S : Scheme.{u}} (U : Over S)
    (E : ModuleDerived (ofOver U)) (E0 : Scheme.DerivedQCoh U.left) :
    Nonempty (EpsilonStarComparisonIso U E E0) ↔ isEpsilonStarPullback U E E0 :=
  sorry

/-- Given comparison isomorphisms `α` and `β`, there is a unique `e : E0 ≅ E0'` whose image
under étale inclusion after `ε*` equals `α.inv ≫ β`. -/
theorem epsilonStarComparison_unique {S : Scheme.{u}} (U : Over S)
    {E : ModuleDerived (ofOver U)} {E0 E0' : Scheme.DerivedQCoh U.left}
    (α : EpsilonStarComparisonIso U E E0) (β : EpsilonStarComparisonIso U E E0') :
    ∃! e : E0 ≅ E0',
      (epsilonStar U.left ⋙ SmallEtale.inclusion U.left).map e.hom = α.inv ≫ β.hom :=
  sorry

/-- If `E` lies in `D_QCoh(𝒪_{ofOver U})`, then `E` is the pullback of an object of
`D_QCoh(𝒪_{U.left})` along `ε*` after the `schemeEtaleRingedHom` identification, unique up
to a unique comparison-compatible isomorphism. -/
theorem qcohScheme_unique {S : Scheme.{u}} (U : Over S)
    {E : ModuleDerived (ofOver U)}
    (hE : derivedQuasiCoherentModuleProperty (ofOver U) E) :
    ∃ E0 : Scheme.DerivedQCoh U.left,
      isEpsilonStarPullback U E E0 ∧
        ∀ (E0' : Scheme.DerivedQCoh U.left),
          isEpsilonStarPullback U E E0' →
            ∀ (α : EpsilonStarComparisonIso U E E0)
              (β : EpsilonStarComparisonIso U E E0'),
              ∃! e : E0 ≅ E0',
                (epsilonStar U.left ⋙ SmallEtale.inclusion U.left).map e.hom =
                  α.inv ≫ β.hom :=
  sorry

namespace IsMPseudoCoherentOver

/-- Section 37.59 affine-cover criterion for relative `m`-pseudo-coherence of a derived
module on a scheme, including the finite-type hypothesis on each affine chart. -/
def onScheme {X S : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ) : Prop :=
  ∃ 𝒱 : S.AffineOpenCover.{u}, ∀ j : 𝒱.I₀,
    ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover.{u}, ∀ i : 𝒰.I₀,
      (Scheme.Hom.appTop (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j)).hom.FiniteType ∧
        ∃ (n : ℕ)
          (ι : Spec (𝒰.X i) ⟶
            AffineSpace (ULift.{u} (Fin n)) (Spec (𝒱.X j))),
          AlgebraicGeometry.IsClosedImmersion ι ∧
            ι ≫ (AffineSpace (ULift.{u} (Fin n)) (Spec (𝒱.X j)) ↘ Spec (𝒱.X j)) =
              𝒰.f i ≫ 𝒱.openCover.pullbackHom f j ∧
            RingedSpace.ModuleDerived.IsMPseudoCoherent
              ((RingedSpace.moduleDerivedPushforward ι.toShHom).obj
                ((Scheme.DerivedQCoh.OpenImmersion.exactPullback
                    (𝒰.f i ≫ (𝒱.openCover.pullback₁ f).f j)).mapDerivedCategory.obj
                  E))
              m

/-- The scheme-level affine-cover criterion unfolds to compatible affine charts with a
finite-type hypothesis and an affine-space closed-immersion test. -/
theorem onScheme_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ) :
    onScheme f E m ↔
      ∃ 𝒱 : S.AffineOpenCover.{u}, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover.{u}, ∀ i : 𝒰.I₀,
          (Scheme.Hom.appTop (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j)).hom.FiniteType ∧
            ∃ (n : ℕ)
              (ι : Spec (𝒰.X i) ⟶
                AffineSpace (ULift.{u} (Fin n)) (Spec (𝒱.X j))),
              AlgebraicGeometry.IsClosedImmersion ι ∧
                ι ≫ (AffineSpace (ULift.{u} (Fin n)) (Spec (𝒱.X j)) ↘
                  Spec (𝒱.X j)) =
                  𝒰.f i ≫ 𝒱.openCover.pullbackHom f j ∧
                RingedSpace.ModuleDerived.IsMPseudoCoherent
                  ((RingedSpace.moduleDerivedPushforward ι.toShHom).obj
                    ((Scheme.DerivedQCoh.OpenImmersion.exactPullback
                        (𝒰.f i ≫ (𝒱.openCover.pullback₁ f).f j)).mapDerivedCategory.obj
                      E))
                  m :=
  sorry

/-- On representable algebraic spaces, the phrase that a quasi-coherent derived module `E`
is `m`-pseudo-coherent relative to `Y` means that the unique `E0` of Lemma 75.4.2 satisfies
the Section 37.59 criterion relative to `Y0`. -/
def ofOver {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    [LocallyOfFiniteType (ofOverMap f0)]
    (E : ModuleDerived (AlgebraicSpace.ofOver X0))
    (hE : derivedQuasiCoherentModuleProperty (AlgebraicSpace.ofOver X0) E)
    (m : ℤ) : Prop :=
  ∀ E0 : Scheme.DerivedQCoh X0.left,
    isEpsilonStarPullback X0 E E0 → onScheme f0.left E0.obj m

/-- Representable relative `m`-pseudo-coherence is the Section 37.59 criterion on some
(hence the unique) `ε*` preimage of `E`. -/
theorem ofOver_iff {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    [LocallyOfFiniteType (ofOverMap f0)]
    (E : ModuleDerived (AlgebraicSpace.ofOver X0))
    (hE : derivedQuasiCoherentModuleProperty (AlgebraicSpace.ofOver X0) E)
    (m : ℤ) :
    ofOver f0 E hE m ↔
      ∃ E0 : Scheme.DerivedQCoh X0.left,
        isEpsilonStarPullback X0 E E0 ∧ onScheme f0.left E0.obj m :=
  sorry

/-- Representable relative `m`-pseudo-coherence yields the Section 37.59 criterion on
any `E0` whose `ε*` recovers `E`. -/
theorem ofOver_spec {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    [LocallyOfFiniteType (ofOverMap f0)]
    {E : ModuleDerived (AlgebraicSpace.ofOver X0)}
    {hE : derivedQuasiCoherentModuleProperty (AlgebraicSpace.ofOver X0) E}
    {m : ℤ} (h : ofOver f0 E hE m) {E0 : Scheme.DerivedQCoh X0.left}
    (hE0 : isEpsilonStarPullback X0 E E0) :
    onScheme f0.left E0.obj m :=
  sorry

end IsMPseudoCoherentOver

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
