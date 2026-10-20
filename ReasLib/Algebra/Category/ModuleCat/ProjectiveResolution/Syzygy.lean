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
    kernelSyzygy P 0 = M := sorry

/-- The first explicit syzygy is the kernel of the augmentation. -/
@[simp, stacks 0CXC "first explicit syzygy"]
theorem kernelSyzygy_one (P : CategoryTheory.ProjectiveResolution M) :
    kernelSyzygy P 1 = ModuleCat.of R (LinearMap.ker (P.π.f 0).hom) := sorry

/-- A higher explicit syzygy is the kernel of the corresponding differential. -/
@[simp, stacks 0CXC "higher explicit syzygy"]
theorem kernelSyzygy_succ_succ (P : CategoryTheory.ProjectiveResolution M) (n : ℕ) :
    kernelSyzygy P (n + 2) = ModuleCat.of R (LinearMap.ker (P.complex.d (n + 1) n).hom) := sorry

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
    Projective (kernelSyzygy P d) ↔ Projective (P.syzygy d) := sorry

/-- The explicit kernel representative detects the projective-dimension bound. -/
@[stacks 0CXC "projective dimension from an explicit syzygy"]
theorem projective_iff_dimLE (P : CategoryTheory.ProjectiveResolution M) (d : ℕ) :
    Projective (kernelSyzygy P d) ↔ HasProjectiveDimensionLE M d := sorry

/-- A projective-dimension bound makes the explicit kernel representative of every chosen
projective resolution projective.

This is the calculation-oriented counterpart of the canonical theorem for `P.syzygy`; it is useful
when a downstream module argument must use the literal `LinearMap.ker` representative. -/
@[stacks 0CXC "projective explicit syzygy from projective dimension"]
theorem projective_of_dimLE (P : CategoryTheory.ProjectiveResolution M) {d : ℕ}
    (hM : HasProjectiveDimensionLE M d) :
    Projective (kernelSyzygy P d) := sorry

/-- A projective explicit kernel representative gives the corresponding projective-dimension
bound. -/
@[stacks 0CXC "projective dimension from a projective explicit syzygy"]
theorem dimLE_of_projective (P : CategoryTheory.ProjectiveResolution M) {d : ℕ}
    (hP : Projective (kernelSyzygy P d)) :
    HasProjectiveDimensionLE M d := sorry

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
    P.SyzygyProjective d ↔ Projective (P.syzygy d) := sorry

/-- The degree-zero compatibility view is projectivity of the resolved module. -/
@[stacks 0CXC "degree-zero projective syzygy compatibility view"]
theorem syzygyProjective_zero_iff (P : CategoryTheory.ProjectiveResolution M) :
    P.SyzygyProjective 0 ↔ Projective M := sorry

end CategoryTheory.ProjectiveResolution
