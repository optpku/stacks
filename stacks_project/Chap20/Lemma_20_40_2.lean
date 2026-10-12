/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.ComplexAcyclicity
public import stacks_project.Chap20.Lemma_20_40_1

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u} [Finite ι]

section

variable (𝒰 : ι → Opens X.carrier)

/- Domain-style sampling for Lemma 20.40.2:
- primary domain: alternating Čech-to-derived-global-sections comparisons for complexes of
  `𝒪_X`-modules on a finite open cover;
- sampled owner declarations:
  `moduleAlternatingCechToDerivedFunctor`,
  `cochainToAbelian`,
  `cochainToAbelianUnitApp`,
  `IsModuleAlternatingCechToDerivedGlobalSectionsComparison`,
  `exists_moduleAlternatingCechToDerivedGlobalSections`,
  `SheafOfModules.toSheaf`;
- best owner abstraction: the comparison natural transformation from the alternating Čech total
  complex to abelian-valued derived global sections is already owned by
  `exists_moduleAlternatingCechToDerivedGlobalSections`, with its compatibility recorded by
  `IsModuleAlternatingCechToDerivedGlobalSectionsComparison`; this file is source-facing only in
  adding the basiswise acyclicity criterion that forces the component at one fixed complex `F` to
  be an isomorphism;
- primitive data: the finite cover `𝒰`, the complex `F`, a basis `𝓑` of opens, and the
  basiswise vanishing hypotheses on the underlying abelian sheaves of the terms, cokernels, and
  cohomology sheaves;
- derived API: the existence of the comparison morphism with the same compatibility relation as
  Lemma `20.40.1`, together with `IsIso (τ.app F)`.

Source/core/bridge triage:
- `source-facing`: `exists_moduleAlternatingCechToDerivedGlobalSections_isIso_of_basiswise_acyclicity`;
- `core/canonical`: `moduleAlternatingCechToDerivedFunctor`,
  `cochainToAbelian`,
  `cochainToAbelianUnitApp`,
  `IsModuleAlternatingCechToDerivedGlobalSectionsComparison`, and
  `exists_moduleAlternatingCechToDerivedGlobalSections`;
- `bridge/view`: the basiswise acyclicity hypotheses turning the general comparison of
  Lemma `20.40.1` into an isomorphism at `F`.
-/

-- Proof sketch: for any compatible comparison `τ`, pass to bounded-below truncations `τ_{≥ -n}
-- F`. Lemma `20.23.6` identifies alternating and ordinary Čech total complexes, and
-- Lemma `20.25.2` computes `RΓ(X, τ_{≥ -n} F)` from the ordinary Čech complex using the
-- basiswise acyclicity of the terms. The cokernel and cohomology-sheaf vanishing hypotheses let
-- one pass to a truncation-limit injective resolution as in Lemma `20.38.1`; the resulting
-- inverse systems are eventually constant in each total degree because the alternating Čech
-- complex is finite. Applying the Milnor-type limit comparison then shows that `τ.app F` is an
-- isomorphism in `D(Ab)`.
/-- A compatible alternating Čech comparison is invertible at a complex satisfying the canonical
basiswise acyclicity predicate. -/
theorem isIso_app_of_basiswise_acyclicity
    (F : CochainComplex (RingedSpace.Modules X) ℤ)
    {𝓑 : Set (Opens X.carrier)}
    (h𝓑 : Opens.IsBasis 𝓑)
    (τ : moduleAlternatingCechToDerivedFunctor X 𝒰 ⟶
      (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤
        DerivedCategory (RingedSpace.Modules X)) ⋙ toAbelian X)
    (hτ : IsModuleAlternatingCechToDerivedGlobalSectionsComparison X 𝒰 τ)
    (hacyclic : ModuleCech.BasiswiseAcyclic 𝒰 F 𝓑) :
    IsIso (τ.app F) := sorry

/-- Lemma 20.40.2: for a finite open covering `𝒰` with `iSup 𝒰 = ⊤` of a ringed space
`(X, 𝒪_X)`, assume `𝓑` is a basis of opens of `X`, every finite intersection of members of `𝒰`
lies in `𝓑`, and for every `U ∈ 𝓑`, every `p > 0`, and every `q : ℤ`, the higher cohomology
groups of the underlying abelian sheaves of `F.X q`, `cokernel (F.d (q - 1) q)`, and
`F.homology q` vanish on `U`. Then there exists a comparison morphism of Lemma `20.40.1` from the
total alternating Čech complex of `F` to `RΓ(X, F)` whose component at `F` is an isomorphism in
`D(AddCommGrpCat)`. -/
@[stacks 08C2]
theorem exists_moduleAlternatingCechToDerivedGlobalSections_isIso_of_basiswise_acyclicity
    (h𝒰 : iSup 𝒰 = ⊤)
    (F : CochainComplex (RingedSpace.Modules X) ℤ)
    {𝓑 : Set (Opens X.carrier)}
    (h𝓑 : Opens.IsBasis 𝓑)
    (hacyclic : ModuleCech.UnderlyingBasiswiseAcyclic 𝒰 F 𝓑) :
    ∃ τ : moduleAlternatingCechToDerivedFunctor X 𝒰 ⟶
        (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤
          DerivedCategory (RingedSpace.Modules X)) ⋙ toAbelian X,
      IsModuleAlternatingCechToDerivedGlobalSectionsComparison X 𝒰 τ ∧
        IsIso (τ.app F) := sorry

end

end AlgebraicGeometry.RingedSpace
