/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import ReasLib.CategoryTheory.Abelian.Projective.Resolution.Syzygy
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Concrete syzygies in `ModuleCat`

@stack 0CXC

The canonical syzygy of a categorical projective resolution is
`CategoryTheory.ProjectiveResolution.syzygy`.  Module calculations often need the explicit
submodule kernel, however.  This leaf owns that concrete presentation and the canonical
isomorphism back to the categorical owner.  Projectivity and projective-dimension statements
should use the latter through the bridge namespace below; no second projective-syzygy predicate is
introduced.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.ModuleCat.ProjectiveResolution

variable {R : Type u} [Ring R]
variable {M : ModuleCat.{v} R}

/-- The explicit `ModuleCat` representative of the syzygy tower of `P`.

Degree `0` is the target, degree `1` is the kernel of the augmentation, and degree `n + 2` is the
kernel of the differential from degree `n + 2` to degree `n + 1`.  This is a calculation view of
the canonical object `P.syzygy`; it is not a second syzygy notion.
-/
@[stacks 0CXC "explicit module representative of a projective-resolution syzygy"]
noncomputable def kernelSyzygy (P : CategoryTheory.ProjectiveResolution M) :
    ℕ → ModuleCat.{v} R
  | 0 => M
  | 1 => ModuleCat.of R (LinearMap.ker (P.π.f 0).hom)
  | n + 2 => ModuleCat.of R (LinearMap.ker (P.complex.d (n + 1) n).hom)

/-- The explicit degree-zero syzygy representative is the resolved module. -/
@[simp, stacks 0CXC "degree-zero explicit syzygy"]
theorem kernelSyzygy_zero (P : CategoryTheory.ProjectiveResolution M) :
    kernelSyzygy P 0 = M := rfl

/-- The first explicit syzygy is the kernel of the augmentation. -/
@[simp, stacks 0CXC "first explicit syzygy"]
theorem kernelSyzygy_one (P : CategoryTheory.ProjectiveResolution M) :
    kernelSyzygy P 1 = ModuleCat.of R (LinearMap.ker (P.π.f 0).hom) := rfl

/-- A higher explicit syzygy is the kernel of the corresponding differential. -/
@[simp, stacks 0CXC "higher explicit syzygy"]
theorem kernelSyzygy_succ_succ (P : CategoryTheory.ProjectiveResolution M) (n : ℕ) :
    kernelSyzygy P (n + 2) = ModuleCat.of R (LinearMap.ker (P.complex.d (n + 1) n).hom) := rfl

namespace kernelSyzygy

/-- The ambient categorical kernel is canonically isomorphic to the concrete submodule kernel.

The two limit cones are supplied explicitly, so this bridge does not depend on which kernel
instance happens to be selected by a downstream `ModuleCat` section.
-/
@[stacks 0CXC "categorical and concrete module kernels"]
abbrev kernelIsoKer {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    kernel f ≅ ModuleCat.of R f.hom.ker :=
  ModuleCat.kernelIsoKer f

/-- The canonical kernel isomorphism identifies the concrete subtype inclusion with the categorical
kernel inclusion. -/
@[simp, stacks 0CXC "explicit kernel inclusion bridge"]
abbrev kernelIsoKer_hom_comp_subtype {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    (kernelSyzygy.kernelIsoKer f).hom ≫ ModuleCat.ofHom f.hom.ker.subtype = kernel.ι f :=
  ModuleCat.kernelIsoKer_hom_ker_subtype f

/-- The inverse kernel isomorphism recovers the concrete subtype inclusion. -/
@[simp, stacks 0CXC "explicit kernel inclusion inverse bridge"]
abbrev kernelIsoKer_inv_comp_ι {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    (kernelSyzygy.kernelIsoKer f).inv ≫ kernel.ι f = ModuleCat.ofHom f.hom.ker.subtype :=
  ModuleCat.kernelIsoKer_inv_kernel_ι f

/-- The canonical isomorphism from the categorical syzygy to its explicit module representative. -/
@[stacks 0CXC "categorical-to-explicit syzygy isomorphism"]
noncomputable def syzygyIsoKernel (P : CategoryTheory.ProjectiveResolution M) :
    (d : ℕ) → P.syzygy d ≅ kernelSyzygy P d
  | 0 => Iso.refl M
  | 1 => kernelSyzygy.kernelIsoKer (P.π.f 0)
  | n + 2 => kernelSyzygy.kernelIsoKer (P.complex.d (n + 1) n)

/-- Projectivity is unchanged when the categorical syzygy is represented by a submodule kernel. -/
@[stacks 0CXC "projectivity of an explicit syzygy"]
theorem projective_iff (P : CategoryTheory.ProjectiveResolution M) (d : ℕ) :
    Projective (kernelSyzygy P d) ↔ Projective (P.syzygy d) :=
  (Projective.iso_iff (syzygyIsoKernel P d)).symm

private theorem kernel_lift_shortExact {A B C : ModuleCat.{v} R}
    (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
    (h : (ShortComplex.mk f g w).Exact) :
    (ShortComplex.mk (kernel.ι f) (kernel.lift g f w) (by
      apply (cancel_mono (kernel.ι g)).1
      simp only [Category.assoc, kernel.lift_ι, kernel.condition, zero_comp])).ShortExact := by
  let S := ShortComplex.mk (kernel.ι f) (kernel.lift g f w) (by
    apply (cancel_mono (kernel.ι g)).1
    simp only [Category.assoc, kernel.lift_ι, kernel.condition, zero_comp])
  change S.ShortExact
  haveI : Epi S.g := h.epi_kernelLift
  refine { exact := ?_ }
  let φ : S ⟶ ShortComplex.mk (kernel.ι f) f (kernel.condition f) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι g
      comm₁₂ := by simp [S]
      comm₂₃ := by simp [S] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (ShortComplex.exact_kernel f)

/-- The explicit kernel representative detects the projective-dimension bound. -/
@[stacks 0CXC "projective dimension from an explicit syzygy"]
theorem projective_iff_dimLE (P : CategoryTheory.ProjectiveResolution M) (d : ℕ) :
    Projective (kernelSyzygy P d) ↔ HasProjectiveDimensionLE M d := by
  have hzero (n : ℕ) : P.inclusion n ≫ P.toSyzygy n = 0 := by
    cases n with
    | zero => exact kernel.condition (P.π.f 0)
    | succ n =>
      cases n with
      | zero =>
        change kernel.ι (P.complex.d 1 0) ≫
          kernel.lift (P.π.f 0) (P.complex.d 1 0) _ = 0
        apply (cancel_mono (kernel.ι (P.π.f 0))).1
        simp only [Category.assoc, kernel.lift_ι, kernel.condition, zero_comp]
      | succ n =>
        change kernel.ι (P.complex.d (n + 2) (n + 1)) ≫
          kernel.lift (P.complex.d (n + 1) n) (P.complex.d (n + 2) (n + 1)) _ = 0
        apply (cancel_mono (kernel.ι (P.complex.d (n + 1) n))).1
        simp only [Category.assoc, kernel.lift_ι, kernel.condition, zero_comp]
  have hS (n : ℕ) :
      (ShortComplex.mk (P.inclusion n) (P.toSyzygy n) (hzero n)).ShortExact := by
    cases n with
    | zero =>
      change (ShortComplex.mk (kernel.ι (P.π.f 0)) (P.π.f 0) (kernel.condition _)).ShortExact
      exact { exact := ShortComplex.exact_kernel (P.π.f 0) }
    | succ n =>
      cases n with
      | zero =>
        exact kernel_lift_shortExact _ _ P.complex_d_comp_π_f_zero P.exact₀
      | succ n =>
        exact kernel_lift_shortExact _ _ (P.complex.d_comp_d (n + 2) (n + 1) n)
          (P.exact_succ n)
  have hdim (k n : ℕ) :
      HasProjectiveDimensionLE (P.syzygy k) n ↔ HasProjectiveDimensionLE M (k + n) := by
    induction k generalizing n with
    | zero =>
      change HasProjectiveDimensionLE M n ↔ HasProjectiveDimensionLE M (0 + n)
      rw [Nat.zero_add]
    | succ k ih =>
      have hshift := (hS k).hasProjectiveDimensionLT_X₃_iff n (P.projective k)
      exact hshift.symm.trans (by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using ih (n + 1))
  exact (projective_iff P d).trans
    ((projective_iff_hasProjectiveDimensionLE_zero (P.syzygy d)).trans (by
      simpa only [Nat.add_zero] using hdim d 0))

/-- A projective-dimension bound makes the explicit kernel representative of every chosen
projective resolution projective.

This is the calculation-oriented counterpart of the canonical theorem for `P.syzygy`; it is useful
when a downstream module argument must use the literal `LinearMap.ker` representative. -/
@[stacks 0CXC "projective explicit syzygy from projective dimension"]
theorem projective_of_dimLE (P : CategoryTheory.ProjectiveResolution M) {d : ℕ}
    (hM : HasProjectiveDimensionLE M d) :
    Projective (kernelSyzygy P d) :=
  (projective_iff_dimLE P d).2 hM

/-- A projective explicit kernel representative gives the corresponding projective-dimension
bound. -/
@[stacks 0CXC "projective dimension from a projective explicit syzygy"]
theorem dimLE_of_projective (P : CategoryTheory.ProjectiveResolution M) {d : ℕ}
    (hP : Projective (kernelSyzygy P d)) :
    HasProjectiveDimensionLE M d :=
  (projective_iff_dimLE P d).1 hP

end kernelSyzygy

end CategoryTheory.ModuleCat.ProjectiveResolution

namespace CategoryTheory.ProjectiveResolution

variable {R : Type u} [Ring R]
variable {M : ModuleCat.{v} R}

/-- Compatibility view for source-facing statements that name a projective syzygy.

The canonical proposition is `Projective (P.syzygy d)`.  This historical name deliberately points
to the explicit `ModuleCat` kernel representative so existing module consumers keep their source
shape; `kernelSyzygy.projective_iff` transports it to the canonical owner.  New reusable APIs
should state `Projective (P.syzygy d)` or, when literal kernels matter,
`Projective (ModuleCat.ProjectiveResolution.kernelSyzygy P d)` directly.
-/
@[stacks 0CXC "compatibility view for projective explicit syzygies"]
abbrev SyzygyProjective (P : CategoryTheory.ProjectiveResolution M) (d : ℕ) : Prop :=
  Projective (CategoryTheory.ModuleCat.ProjectiveResolution.kernelSyzygy P d)

/-- The compatibility view is equivalent to projectivity of the canonical categorical syzygy. -/
@[stacks 0CXC "canonical projective syzygy compatibility bridge"]
theorem syzygyProjective_iff (P : CategoryTheory.ProjectiveResolution M) (d : ℕ) :
    P.SyzygyProjective d ↔ Projective (P.syzygy d) :=
  ModuleCat.ProjectiveResolution.kernelSyzygy.projective_iff P d

/-- The degree-zero compatibility view is projectivity of the resolved module. -/
@[stacks 0CXC "degree-zero projective syzygy compatibility view"]
theorem syzygyProjective_zero_iff (P : CategoryTheory.ProjectiveResolution M) :
    P.SyzygyProjective 0 ↔ Projective M := Iff.rfl

end CategoryTheory.ProjectiveResolution
