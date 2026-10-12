/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap20.Lemma_20_25_1
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Acyclicity

/-! @stack 0FLH -/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}
/- Domain-style sampling for Lemma 20.25.2:
- primary domain: Čech-to-derived-global-sections comparison for bounded-below complexes of
  `𝒪_X`-modules on a ringed space;
- sampled owner declarations:
  `moduleCechDerivedFunctor`,
  `Module.Derived.Sections.Bounded.functor`,
  `Functor.RightDerived.Bounded.functor`,
  `exists_moduleCechToDerivedGlobalSections`,
  `IsModuleCechToDerivedGlobalSectionsComparison`,
  `exists_moduleCechToDerivedGlobalSectionsSpectralSequence`;
- best owner abstraction: the canonical functors
  `moduleCechDerivedFunctor X 𝒰` and the canonical bounded-below derived-sections owner
  `Module.Derived.Sections.Bounded.functor X (⊤ : Opens X.carrier)`, with this file keeping only
  the source-facing objectwise comparison theorem under the acyclicity hypothesis.

Source/core/bridge triage:
- `source-facing`: the objectwise isomorphism
  `Tot(Čech^•(𝒰, K)) ≅ RΓ(X, K)` under the vanishing-on-intersections hypothesis;
- `core/canonical`: `moduleCechDerivedFunctor X 𝒰`,
  `Module.Derived.Sections.Bounded.functor X (⊤ : Opens X.carrier)`,
  `Functor.RightDerived.Bounded.functor (moduleGlobalSectionsFunctor X)`, the comparison
  predicate
  `IsModuleCechToDerivedGlobalSectionsComparison X 𝒰`, and the spectral-sequence owners from
  `Lemma_20_25_1`;
- `bridge/view`: the passage from a module to its underlying additive sheaf on each Čech
  intersection via the canonical owner `moduleUnderlyingSheaf`.

Primitive data versus derived API:
- primitive data: the cover `𝒰`, the cover equality `h𝒰`, the bounded-below complex `K`, and the
  vanishing hypothesis on the terms of `K` over each finite Čech intersection;
- derived API: the source-facing theorem `Lemma 20.25.2`, stating that any comparison morphism
  with the injective-case computation property from `Lemma_20_25_1` is an isomorphism on `K`,
  together with the thin existential corollary obtained by choosing such a comparison from
  `exists_moduleCechToDerivedGlobalSections`. No extra local comparison morphism owner is
  introduced.
-/

section

variable (𝒰 : ι → Opens X.carrier)

local notation "Kplus" => CochainComplex.Plus X.Modules
local notation "CechF" => moduleCechDerivedFunctor X 𝒰
local notation "KplusToDplusModX" =>
  (DerivedCategory.Plus.Q : Kplus ⥤ DerivedCategory.Plus X.Modules)
local notation "RΓplus" =>
  Module.Derived.GlobalSections.Bounded.functor X

-- Proof sketch: apply the Čech-to-hypercohomology spectral sequence from Lemma `20.25.1`. The
-- hypothesis says that for every fixed internal degree `q`, the higher cohomology of `K.X q` on
-- every finite intersection of the cover vanishes, so the spectral sequence is concentrated on the
-- `p = 0` row. Therefore any comparison of Lemma `20.25.1` is an isomorphism on `K`.
/-- Lemma 20.25.2: if `τ` is a comparison morphism of Lemma `20.25.1` and every
positive-degree cohomology group of each term `K.obj.X q` vanishes on every finite intersection of
the open cover `𝒰`, then `τ.app K` is an isomorphism. -/
@[stacks 0FLH]
theorem isIso_app_of_acyclic_on_intersections
    (τ : CechF ⟶ KplusToDplusModX ⋙ RΓplus)
    (K : Kplus)
    (hτ : IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ)
    (hacyclic : ∀ q : ℤ,
      ModuleCech.IsAcyclicOnIntersections 𝒰 (K.obj.X q)) :
    IsIso (τ.app K) := sorry

/-- Companion corollary to Lemma `20.25.2`: one may choose a comparison morphism of
Lemma `20.25.1` whose component at `K` is an isomorphism. -/
theorem exists_moduleCechToDerivedGlobalSections_isIso_app_of_acyclic_on_intersections
    (h𝒰 : iSup 𝒰 = ⊤)
    (K : Kplus)
    (hacyclic : ∀ q : ℤ,
      ModuleCech.IsAcyclicOnIntersections 𝒰 (K.obj.X q)) :
    ∃ τ : CechF ⟶ KplusToDplusModX ⋙ RΓplus,
      IsModuleCechToDerivedGlobalSectionsComparison X 𝒰 τ ∧ IsIso (τ.app K) := sorry

end

end AlgebraicGeometry.RingedSpace
