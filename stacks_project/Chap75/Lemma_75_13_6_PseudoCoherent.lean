/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Localization
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh

/-!
# Pseudo-coherent derived modules on algebraic spaces

The ringed-site `m`-pseudo-coherence predicates require `UnivLE` between the site universe and
the ring universe, which fails for the small étale site of an algebraic space.  The predicates
below are the same representative-based local strict-perfect approximation, stated directly on
`D(𝒪_X)` and on complexes of `𝒪_X`-modules.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The category of module sheaves on a slice of the small étale site is abelian. -/
instance localizationModulesAbelian {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : smallEtaleSite X) :
    Abelian (RingedSite.ModuleCat.{u} ((ringedSite X).localization U)) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

namespace CochainComplex

/-- A complex of `𝒪_X`-modules is `m`-pseudo-coherent if locally it admits a map from a
strictly perfect complex inducing cohomology isomorphisms above `m` and an epimorphism in
degree `m`. -/
def IsMPseudoCoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : _root_.CochainComplex (Modules X) ℤ) (m : ℤ) : Prop :=
  ∀ U : ringedSite X, ∃ T : (ringedSite X).siteTopology.Cover U, ∀ I : T.Arrow,
    ∃ E' : _root_.CochainComplex
        (RingedSite.ModuleCat.{u} ((ringedSite X).localization I.Y)) ℤ,
      SheafOfModules.CochainComplex.IsStrictlyPerfect E' ∧
        ∃ alpha :
            E' ⟶ (RingedSite.Hom.localizedRestrictionComplex.{u} (ringedSite X) I.Y).obj E,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap alpha j)) ∧
            Epi (HomologicalComplex.homologyMap alpha m)

/-- A complex of `𝒪_X`-modules is pseudo-coherent if it is `m`-pseudo-coherent for every
integer `m`. -/
def IsPseudoCoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : _root_.CochainComplex (Modules X) ℤ) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherent E m

end CochainComplex

/-- An `m`-pseudo-coherent derived `𝒪_X`-module on an algebraic space. -/
def IsMPseudoCoherent {S : Scheme.{u}} (X : AlgebraicSpace S)
    (E : ModuleDerived X) (m : ℤ) : Prop :=
  ∃ F : _root_.CochainComplex (Modules X) ℤ, ∃ _ : E ≅ DerivedCategory.Q.obj F,
    CochainComplex.IsMPseudoCoherent F m

/-- A pseudo-coherent derived `𝒪_X`-module on an algebraic space. -/
def IsPseudoCoherent {S : Scheme.{u}} (X : AlgebraicSpace S)
    (E : ModuleDerived X) : Prop :=
  ∃ F : _root_.CochainComplex (Modules X) ℤ, ∃ _ : E ≅ DerivedCategory.Q.obj F,
    CochainComplex.IsPseudoCoherent F

/-- A derived `𝒪_X`-module on an algebraic space is pseudo-coherent if and only if it is
`m`-pseudo-coherent for every integer `m`. -/
theorem isPseudoCoherent_iff_forall_isMPseudoCoherent
    {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X} :
    IsPseudoCoherent X E ↔ ∀ m : ℤ, IsMPseudoCoherent X E m := sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.PseudoCoherent

/-- The cohomology sheaves of an `m`-pseudo-coherent derived module in degrees strictly above
`m` are quasi-coherent. -/
theorem higherCohomology_isQuasicoherent
    {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X} {m i : ℤ}
    (hE : IsMPseudoCoherent X E m) (hi : m < i) :
    ((DerivedCategory.homologyFunctor (Modules X) i).obj E).IsQuasicoherent := sorry

/-- A pseudo-coherent derived `𝒪_X`-module on an algebraic space lies in `D_QCoh(𝒪_X)`. -/
theorem derivedQuasiCoherentModuleProperty
    {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X}
    (hE : IsPseudoCoherent X E) :
    AlgebraicGeometry.AlgebraicSpace.derivedQuasiCoherentModuleProperty X E := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.PseudoCoherent
