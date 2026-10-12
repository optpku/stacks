/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ModuleEnd

/-!
# Two-periodic complexes from three module endomorphisms

Three endomorphisms whose individual ranges and kernels agree with those of complementary
twofold composites determine complexes on the module, a range, and a kernel quotient.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The first endomorphism has image in the kernel of the composite of the other two. -/
theorem ofComposite_d₀_range_le_ker (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker) :
    alpha.range ≤ (beta.comp gamma).ker := sorry

/-- The composite of the last two endomorphisms has image in the kernel of the first. -/
theorem ofComposite_d₁_range_le_ker (alpha beta gamma : Module.End R M)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    (beta.comp gamma).range ≤ alpha.ker := sorry

/-- The two-periodic complex on `M` with differentials `alpha` and `beta.comp gamma`. -/
def ofComposite (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    TwoPeriodicEndomorphism (ModuleCat R) :=
  ofModuleEnd alpha (beta.comp gamma) (ofComposite_d₀_range_le_ker alpha beta gamma hI)
    (ofComposite_d₁_range_le_ker alpha beta gamma hK)

/-- The carrier of `ofComposite` is `M`. -/
@[simp]
theorem ofComposite_X (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    (ofComposite alpha beta gamma hI hK).X = ModuleCat.of R M := sorry

/-- The degree-zero differential of `ofComposite` is `alpha`. -/
@[simp]
theorem ofComposite_d₀ (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    (ofComposite alpha beta gamma hI hK).d₀ = ModuleCat.ofHom alpha := sorry

/-- The degree-one differential of `ofComposite` is `beta.comp gamma`. -/
@[simp]
theorem ofComposite_d₁ (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    (ofComposite alpha beta gamma hI hK).d₁ = ModuleCat.ofHom (beta.comp gamma) := sorry

/-- The image of `gamma` is invariant under `alpha`. -/
theorem onRange_alpha_mem (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    ∀ x ∈ gamma.range, alpha x ∈ gamma.range := sorry

/-- The image of `gamma` is invariant under `beta`. -/
theorem onRange_beta_mem (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    ∀ x ∈ gamma.range, beta x ∈ gamma.range := sorry

/-- On `range gamma`, the restricted map induced by `alpha` has image in the kernel of
the restricted map induced by `beta`. -/
theorem onRange_d₀_range_le_ker (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    (alpha.restrict (onRange_alpha_mem alpha beta gamma hI hK)).range ≤
      (beta.restrict (onRange_beta_mem alpha beta gamma hI hK)).ker := sorry

/-- On `range gamma`, the restricted map induced by `beta` has image in the kernel of
the restricted map induced by `alpha`. -/
theorem onRange_d₁_range_le_ker (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    (beta.restrict (onRange_beta_mem alpha beta gamma hI hK)).range ≤
      (alpha.restrict (onRange_alpha_mem alpha beta gamma hI hK)).ker := sorry

/-- The two-periodic complex on `range gamma` with the restrictions of `alpha` and `beta`. -/
def onRange (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    TwoPeriodicEndomorphism (ModuleCat R) :=
  ofModuleEnd (alpha.restrict (onRange_alpha_mem alpha beta gamma hI hK))
    (beta.restrict (onRange_beta_mem alpha beta gamma hI hK))
    (onRange_d₀_range_le_ker alpha beta gamma hI hK)
    (onRange_d₁_range_le_ker alpha beta gamma hI hK)

/-- The carrier of `onRange` is `range gamma`. -/
@[simp]
theorem onRange_X (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    (onRange alpha beta gamma hI hK).X = ModuleCat.of R gamma.range := sorry

/-- The degree-zero differential of `onRange` acts by `alpha`. -/
@[simp]
theorem onRange_d₀_apply (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) (x : gamma.range) :
    ((onRange alpha beta gamma hI hK).d₀.hom x).val = alpha x := sorry

/-- The degree-one differential of `onRange` acts by `beta`. -/
@[simp]
theorem onRange_d₁_apply (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) (x : gamma.range) :
    ((onRange alpha beta gamma hI hK).d₁.hom x).val = beta x := sorry

/-- The kernel of `beta` is invariant under `alpha`. -/
theorem onKerQuotient_alpha_le_comap (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    beta.ker ≤ beta.ker.comap alpha := sorry

/-- The kernel of `beta` is invariant under `gamma`. -/
theorem onKerQuotient_gamma_le_comap (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    beta.ker ≤ beta.ker.comap gamma := sorry

/-- On the quotient by `ker beta`, the map induced by `alpha` has image in the kernel
of the map induced by `gamma`. -/
theorem onKerQuotient_d₀_range_le_ker (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    (beta.ker.mapQ beta.ker alpha (onKerQuotient_alpha_le_comap alpha beta gamma hI hK)).range ≤
      (beta.ker.mapQ beta.ker gamma
        (onKerQuotient_gamma_le_comap alpha beta gamma hI hK)).ker := sorry

/-- On the quotient by `ker beta`, the map induced by `gamma` has image in the kernel
of the map induced by `alpha`. -/
theorem onKerQuotient_d₁_range_le_ker (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    (beta.ker.mapQ beta.ker gamma
      (onKerQuotient_gamma_le_comap alpha beta gamma hI hK)).range ≤
        (beta.ker.mapQ beta.ker alpha
          (onKerQuotient_alpha_le_comap alpha beta gamma hI hK)).ker := sorry

/-- The two-periodic complex on `M ⧸ ker beta` with the endomorphisms induced by `alpha`
and `gamma`. -/
def onKerQuotient (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    TwoPeriodicEndomorphism (ModuleCat R) :=
  ofModuleEnd
    (beta.ker.mapQ beta.ker alpha (onKerQuotient_alpha_le_comap alpha beta gamma hI hK))
    (beta.ker.mapQ beta.ker gamma (onKerQuotient_gamma_le_comap alpha beta gamma hI hK))
    (onKerQuotient_d₀_range_le_ker alpha beta gamma hI hK)
    (onKerQuotient_d₁_range_le_ker alpha beta gamma hI hK)

/-- The carrier of `onKerQuotient` is `M ⧸ ker beta`. -/
@[simp]
theorem onKerQuotient_X (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) :
    (onKerQuotient alpha beta gamma hI hK).X = ModuleCat.of R (M ⧸ beta.ker) := sorry

/-- On quotient representatives, the degree-zero differential of `onKerQuotient` is
induced by `alpha`. -/
@[simp]
theorem onKerQuotient_d₀_apply_mk (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) (x : M) :
    (onKerQuotient alpha beta gamma hI hK).d₀.hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (alpha x) := sorry

/-- On quotient representatives, the degree-one differential of `onKerQuotient` is
induced by `gamma`. -/
@[simp]
theorem onKerQuotient_d₁_apply_mk (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂, List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
      delta₀.ker = (delta₁.comp delta₂).range) (x : M) :
    (onKerQuotient alpha beta gamma hI hK).d₁.hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (gamma x) := sorry

end CategoryTheory.TwoPeriodicEndomorphism
