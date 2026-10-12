/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap75.Definition_75_3_2_SupportedOn
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent

/-!
# Perfect approximation on algebraic spaces

A closed subset `T` of `Points X`, an object `E` of `DerivedQCoh X`, and an integer
`m` form a triple for which approximation holds when a perfect object of `D(𝒪_X)`
supported on `T` maps to `E` by a morphism that is a cohomology isomorphism in every
degree strictly above `m` and an epimorphism in degree `m`.

The ringed-site perfectness predicates require `UnivLE` between the site universe and
the ring universe, which fails for the small étale site of an algebraic space. Perfectness
below is the same representative-based local strictly perfect quasi-isomorphism used for
pseudo-coherence, stated directly on `D(𝒪_X)` and on complexes of `𝒪_X`-modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace CochainComplex

/-- A complex of `𝒪_X`-modules is perfect if every object of the small étale site has a
cover on which the restricted complex receives a map from a strictly perfect complex
inducing cohomology isomorphisms in every degree. -/
def IsPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : _root_.CochainComplex (Modules X) ℤ) : Prop :=
  ∀ U : ringedSite X, ∃ T : (ringedSite X).siteTopology.Cover U, ∀ I : T.Arrow,
    ∃ E' : _root_.CochainComplex
        (RingedSite.ModuleCat.{u} ((ringedSite X).localization I.Y)) ℤ,
      SheafOfModules.CochainComplex.IsStrictlyPerfect E' ∧
        ∃ alpha :
            E' ⟶ (RingedSite.Hom.localizedRestrictionComplex.{u} (ringedSite X) I.Y).obj E,
          ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap alpha j)

/-- Perfectness of a complex of `𝒪_X`-modules unfolds to strictly perfect local models
inducing cohomology isomorphisms on a cover of every étale object. -/
theorem isPerfect_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : _root_.CochainComplex (Modules X) ℤ) :
    IsPerfect E ↔
      ∀ U : ringedSite X, ∃ T : (ringedSite X).siteTopology.Cover U, ∀ I : T.Arrow,
        ∃ E' : _root_.CochainComplex
            (RingedSite.ModuleCat.{u} ((ringedSite X).localization I.Y)) ℤ,
          SheafOfModules.CochainComplex.IsStrictlyPerfect E' ∧
            ∃ alpha :
                E' ⟶ (RingedSite.Hom.localizedRestrictionComplex.{u} (ringedSite X) I.Y).obj E,
              ∀ j : ℤ, IsIso (HomologicalComplex.homologyMap alpha j) := sorry

end CochainComplex

namespace ModuleDerived

/-- An object of `D(𝒪_X)` is perfect when it is isomorphic to the image of a perfect
complex of `𝒪_X`-modules. -/
abbrev IsPerfect {S : Scheme.{u}} {X : AlgebraicSpace S} (P : ModuleDerived X) : Prop :=
  ∃ F : _root_.CochainComplex (Modules X) ℤ, ∃ _ : P ≅ DerivedCategory.Q.obj F,
    CochainComplex.IsPerfect F

/-- Perfectness of a derived `𝒪_X`-module is equivalent to the existence of a perfect
complex representative. -/
theorem isPerfect_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (P : ModuleDerived X) :
    IsPerfect P ↔
      ∃ F : _root_.CochainComplex (Modules X) ℤ, ∃ _ : P ≅ DerivedCategory.Q.obj F,
        CochainComplex.IsPerfect F := sorry

end ModuleDerived

/-- Approximation holds for a closed subset `T` of `Points X`, an object `E` of
`DerivedQCoh X`, and an integer `m` when some perfect object of `D(𝒪_X)` supported on
`T` maps to `E` by a morphism inducing cohomology isomorphisms in degrees `i` with
`m < i` and an epimorphism in degree `m`. -/
def HasPerfectApproximation {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) (E : DerivedQCoh X) (m : ℤ) : Prop :=
  ∃ P : ModuleDerived X,
    ModuleDerived.IsPerfect P ∧
      ModuleDerived.IsSupportedOn P T ∧
        ∃ α : P ⟶ E.obj,
          (∀ i : ℤ, m < i →
            IsIso ((DerivedCategory.homologyFunctor (Modules X) i).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor (Modules X) m).map α)

/-- The existential characterization of a perfect approximation supported on a closed
subset. -/
theorem hasPerfectApproximation_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) (E : DerivedQCoh X) (m : ℤ) :
    HasPerfectApproximation T E m ↔
      ∃ P : ModuleDerived X,
        ModuleDerived.IsPerfect P ∧
          ModuleDerived.IsSupportedOn P T ∧
            ∃ α : P ⟶ E.obj,
              (∀ i : ℤ, m < i →
                IsIso ((DerivedCategory.homologyFunctor (Modules X) i).map α)) ∧
              Epi ((DerivedCategory.homologyFunctor (Modules X) m).map α) := sorry

namespace HasPerfectApproximation

/-- A perfect supported object and a cohomology isomorphism above `m` with an epimorphism
in degree `m` exhibit a perfect approximation. -/
theorem mk {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T : Closeds (Points X)} {E : DerivedQCoh X} {m : ℤ} {P : ModuleDerived X}
    (hP : ModuleDerived.IsPerfect P) (hT : ModuleDerived.IsSupportedOn P T)
    (α : P ⟶ E.obj)
    (hiso : ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor (Modules X) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (Modules X) m).map α)) :
    HasPerfectApproximation T E m := sorry

/-- Perfect approximation is preserved when the quasi-coherent target is replaced by an
isomorphic derived object. -/
theorem of_iso {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Closeds (Points X)}
    {E F : DerivedQCoh X} {m : ℤ}
    (hE : HasPerfectApproximation T E m) (e : E ≅ F) :
    HasPerfectApproximation T F m := sorry

end HasPerfectApproximation

end AlgebraicGeometry.AlgebraicSpace
