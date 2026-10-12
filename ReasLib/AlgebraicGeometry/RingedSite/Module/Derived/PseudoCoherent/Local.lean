/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization

@[expose] public section

/-!
# Local strict-perfect approximations on ringed sites

This module gives the localized strict-perfect approximation interface used to characterize
pseudo-coherent derived module sheaves.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived localizedRestriction localizedRestrictionDerived)
open RingedSite.CochainComplex (IsStrictlyPerfect)

noncomputable section

universe u v w

set_option checkBinderAnnotations false

namespace RingedSite.DerivedCategory

section

variable {X : RingedSite.{u, v, w}}
variable [UnivLE.{max u v, w}]
variable [∀ U : X, HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction.{w} X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction.{w} X U)]

/-- Definition 21.45.1: a derived object has a strict-perfect approximation in degree `m` over
`U` when its restriction to `X/U` receives a cohomologically suitable map from a strictly perfect
complex. -/
def HasStrictlyPerfectApproximationInDegree
    (K : ModuleDerived.{w} X) (U : X) (m : ℤ) : Prop :=
  ∃ E' : CochainComplex (ModuleCat.{w} (X.localization U)) ℤ,
    IsStrictlyPerfect E' ∧
      ∃ α : DerivedCategory.Q.obj E' ⟶ (localizedRestrictionDerived.{w} X U).obj K,
        (∀ j : ℤ, m < j →
          IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{w} (X.localization U)) j).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor (ModuleCat.{w} (X.localization U)) m).map α)

/-- Strict-perfect approximation data in degree `m` transports across an isomorphism in the
ambient derived category. -/
theorem HasStrictlyPerfectApproximationInDegree.of_iso
    {K L : ModuleDerived.{w} X} (e : K ≅ L) {U : X} {m : ℤ}
    (hK : HasStrictlyPerfectApproximationInDegree K U m) :
    HasStrictlyPerfectApproximationInDegree L U m := sorry

section Relocalization

variable [∀ U : X, ∀ V : X.localization U,
  HasWeakSheafify ((X.localization U).localization V).siteTopology
    AddCommGrpCat.{w}]
variable [∀ U : X, ∀ V : X.localization U,
  ((X.localization U).localization V).siteTopology.WEqualsLocallyBijective
    AddCommGrpCat.{w}]
variable [∀ U : X, ∀ V : X.localization U,
  (localizedRestriction.{w} (X.localization U) V).Additive]
variable [∀ U : X, ∀ V : X.localization U,
  PreservesFiniteLimits (localizedRestriction.{w} (X.localization U) V)]
variable [∀ U : X, ∀ V : X.localization U,
  PreservesFiniteColimits (localizedRestriction.{w} (X.localization U) V)]

/-- Relocalizing along `ρ : U ⟶ V` identifies strict-perfect approximation data after first
restricting to `X/V` with the corresponding data after restricting directly to `X/U`. -/
theorem HasStrictlyPerfectApproximationInDegree.relocalization_iff
    {U V : X} (ρ : U ⟶ V) (K : ModuleDerived.{w} X) (m : ℤ)
    (W : X.localization U) :
    HasStrictlyPerfectApproximationInDegree
        ((localizedRestrictionDerived.{w} X V).obj K) (Over.mk (W.hom ≫ ρ)) m ↔
      HasStrictlyPerfectApproximationInDegree
        ((localizedRestrictionDerived.{w} X U).obj K) W m := sorry

end Relocalization

/-- Definition 21.45.1: an object is `m`-pseudo-coherent exactly when every local restriction
admits a strict-perfect approximation in degree `m` after passage to a covering. -/
theorem isMPseudoCoherent_iff_forall_hasStrictlyPerfectApproximationInDegree
    (K : ModuleDerived.{w} X) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
        HasStrictlyPerfectApproximationInDegree K I.Y m := sorry

/-- Lemma 21.45.2 (1): a strict-perfect approximation on a cover of a terminal object implies
`m`-pseudo-coherence. -/
@[stacks 08FU "(1)"]
theorem isMPseudoCoherent_of_cover_of_isTerminal
    (K : ModuleDerived.{w} X) (m : ℤ) (U : X) (hU : IsTerminal U)
    (hcover : ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
      HasStrictlyPerfectApproximationInDegree K I.Y m) :
    K.IsMPseudoCoherent m := sorry

section Descent

variable [∀ U : X, ∀ V : X.localization U,
  HasWeakSheafify ((X.localization U).localization V).siteTopology
    AddCommGrpCat.{w}]
variable [∀ U : X, ∀ V : X.localization U,
  ((X.localization U).localization V).siteTopology.WEqualsLocallyBijective
    AddCommGrpCat.{w}]

/-- Lemma 21.45.2 (3): `m`-pseudo-coherence descends from a covering family of local
restrictions over every object. -/
@[stacks 08FU "(3)"]
theorem isMPseudoCoherent_of_locally_isMPseudoCoherent
    (K : ModuleDerived.{w} X) (m : ℤ)
    (hlocal : ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
      ((localizedRestrictionDerived.{w} X I.Y).obj K).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m := sorry

end Descent

end

end RingedSite.DerivedCategory
