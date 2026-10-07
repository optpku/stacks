module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.ProjectiveResolution.Bounded
public import ReasLib.Algebra.Category.ModuleCat.ProjectiveResolution.Syzygy
public import ReasLib.CategoryTheory.Abelian.Projective.Resolution.Syzygy

/-!
# Coordinate bounded resolutions and syzygies

This leaf is the bridge between the calculation-oriented coordinate resolution predicate and the
canonical syzygy of a bundled projective resolution.  The top-kernel projectivity criterion itself
is owned by `CategoryTheory.ModuleCat.topKernel_projective_of_exact`; this file only assembles it
with `Coordinate.HasLengthLE`.  Its primary syzygy surface is the canonical `P.syzygy`; the
explicit `kernelSyzygy` surface is a separate `ModuleCat` calculation bridge.

The source-facing chapter names are compatibility views.  New consumers should use the concise
namespace-first declarations in this file, or the canonical categorical declarations when no
coordinate presentation is needed.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.ModuleCat.ProjectiveResolution.Coordinate

variable {R : Type u} [Ring R]
variable {M : ModuleCat.{v} R}

/-- A projective exact prefix whose top kernel is projective gives a coordinate resolution of the
target.  The statement is indexed by the prefix length, so it can be reused independently of any
chosen categorical projective resolution. -/
@[stacks 0CXC "coordinate resolution from an exact projective prefix"]
theorem HasLengthLE.of_exact_topKernel
    {e : ℕ} {M : ModuleCat.{v} R} {F : Fin (e + 2) → ModuleCat.{v} R}
    (hF : ∀ i, Projective (F i))
    (δ : (i : Fin (e + 1)) → F i.succ ⟶ F i.castSucc)
    (π : F 0 ⟶ M)
    (hπ : Function.Surjective π.hom)
    (hExact₀ : Function.Exact (δ 0).hom π.hom)
    (hExact : ∀ i : Fin e, Function.Exact (δ i.succ).hom (δ i.castSucc).hom)
    (htop : Projective (ModuleCat.of R (LinearMap.ker (δ (Fin.last e)).hom))) :
    HasLengthLE M (e + 2) := sorry

/-- A bounded coordinate resolution can be obtained by truncating a projective resolution at a
projective canonical syzygy.  This is the primary reusable source of the finite coordinate witness;
it does not require callers to expose the intermediate differential family. -/
@[stacks 0CXC "coordinate resolution from a projective canonical syzygy"]
theorem HasLengthLE.of_projectiveSyzygy
    (P : CategoryTheory.ProjectiveResolution M) {d : ℕ}
    (hP : Projective (P.syzygy d)) :
    HasLengthLE M d := sorry

/-- A bounded coordinate resolution can be obtained from a projective explicit kernel syzygy.

This is the calculation bridge for consumers which need a literal `LinearMap.ker`; general
categorical consumers should prefer `HasLengthLE.of_projectiveSyzygy`. -/
@[stacks 0CXC "coordinate resolution from a projective explicit syzygy"]
theorem HasLengthLE.of_projectiveKernelSyzygy
    (P : CategoryTheory.ProjectiveResolution M) {d : ℕ}
    (hP : Projective (CategoryTheory.ModuleCat.ProjectiveResolution.kernelSyzygy P d)) :
    HasLengthLE M d := sorry

/-- Compatibility entry point for source-facing statements expressed through
`ProjectiveResolution.SyzygyProjective`.  New APIs should use either the canonical or explicit
kernel bridge above. -/
@[stacks 0CXC "coordinate resolution from a projective syzygy compatibility"]
abbrev HasLengthLE.of_syzygyProjective
    (P : CategoryTheory.ProjectiveResolution M) {d : ℕ}
    (hP : P.SyzygyProjective d) :
    HasLengthLE M d :=
  HasLengthLE.of_projectiveKernelSyzygy P hP

/-- The four reusable formulations of a projective-dimension bound, with a coordinate resolution
and the canonical syzygy of a bundled resolution.

The local resolution-existence assumption is necessary only for the existential clause; it avoids
silently imposing a universe-specific enough-projectives instance on every `ModuleCat` consumer. -/
@[stacks 0CXC "projective dimension coordinate resolution canonical syzygy TFAE"]
theorem projectiveDimensionLE_tfae
    (M : ModuleCat.{v} R) [CategoryTheory.HasProjectiveResolution M] (d : ℕ) :
    List.TFAE
      [ HasProjectiveDimensionLE M d,
        HasLengthLE M d,
        ∃ P : CategoryTheory.ProjectiveResolution M, Projective (P.syzygy d),
        ∀ P : CategoryTheory.ProjectiveResolution M, Projective (P.syzygy d) ] := sorry

/-- The coordinate-resolution TFAE expressed with explicit `ModuleCat` kernel syzygies.

This is intentionally separate from `projectiveDimensionLE_tfae`: it preserves literal kernel
terms for module calculations, while the primary theorem remains independent of that presentation. -/
@[stacks 0CXC "projective dimension coordinate resolution explicit syzygy TFAE"]
theorem projectiveDimensionLE_tfae_kernelSyzygy
    (M : ModuleCat.{v} R) [CategoryTheory.HasProjectiveResolution M] (d : ℕ) :
    List.TFAE
      [ HasProjectiveDimensionLE M d,
        HasLengthLE M d,
        ∃ P : CategoryTheory.ProjectiveResolution M,
          Projective (CategoryTheory.ModuleCat.ProjectiveResolution.kernelSyzygy P d),
        ∀ P : CategoryTheory.ProjectiveResolution M,
          Projective (CategoryTheory.ModuleCat.ProjectiveResolution.kernelSyzygy P d) ] := sorry

end CategoryTheory.ModuleCat.ProjectiveResolution.Coordinate
