/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Finite.Kernel
public import ReasLib.Algebra.Category.ModuleCat.FiniteProjective
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution
public import ReasLib.Algebra.Category.ModuleCat.ProjectiveResolution.Bounded
public import ReasLib.CategoryTheory.Abelian.Projective.Resolution.Syzygy

/-!
# Bounded finite-projective resolutions of modules

This leaf owns `CategoryTheory.ModuleCat.FiniteProjective.HasResolutionLE`, the finite-term,
finite-projective resolution predicate for `ModuleCat`.  `ModuleCat.HasFinProjResLE` is retained as
a transparent compatibility view for existing chapter consumers.  The categorical
bounded-resolution owner lives in `CategoryTheory.ProjectiveResolution.HasLengthLE`; this
module-level predicate is the finite-projective view used by module and commutative-algebra
applications.

The positive-length branch deliberately stores the terms in the full subcategory
`ModuleCat.FiniteProjective`.  Thus finiteness and projectivity are carried by the term owner and
are not repeated as ambient instance arguments at every consumer.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CategoryTheory.ModuleCat

variable {R : Type u} [Ring R]

namespace FiniteProjective

/-- A finite-projective resolution of `M` of length at most `d`.

For `d = 0`, this is finite projectivity of `M`.  For `d = n + 1`, it is the exact finite
sequence `P_{n+1} ⟶ ⋯ ⟶ P₀ ⟶ M`, with surjective augmentation and injective top differential,
where every `Pᵢ` is an object of `ModuleCat.FiniteProjective`. The zero branch is the canonical
predicate `Module.FiniteProjective R M`.
-/
@[stacks 0CXE "finite-projective resolution of bounded length"]
def HasResolutionLE
    (M : ModuleCat.{v} R) (d : ℕ) : Prop :=
  match d with
  | 0 => Module.FiniteProjective R M
  | n + 1 =>
      ∃ (P : Fin (n + 2) → ModuleCat.FiniteProjective.{u, v} R)
        (δ : (i : Fin (n + 1)) → P i.succ ⟶ P i.castSucc)
        (π : (P 0).obj ⟶ M),
        Function.Surjective π.hom ∧
          Function.Exact (δ 0).hom π.hom ∧
          (∀ i : Fin n, Function.Exact (δ i.succ).hom (δ i.castSucc).hom) ∧
          Function.Injective (δ (Fin.last n)).hom

/-- In length zero, the finite-projective resolution predicate is exactly finite projectivity of
the target. -/
@[stacks 0CXE "finite-projective resolution at length zero"]
theorem HasResolutionLE.zero_iff
    (M : ModuleCat.{v} R) :
    HasResolutionLE M 0 ↔ Module.FiniteProjective R M := sorry

/-- Forgetting finite-term data gives a categorical bounded projective resolution. -/
@[stacks 0CXE "finite-projective resolution forgets to a bounded projective resolution"]
theorem HasResolutionLE.hasLengthLE
    {M : ModuleCat.{v} R} {d : ℕ} (hM : HasResolutionLE M d) :
    CategoryTheory.ProjectiveResolution.HasLengthLE M d := sorry

/-- Forgetting finite-term data gives the coordinate projective-resolution presentation.

This is distinct from `HasResolutionLE.hasLengthLE`: the latter lands in the canonical bundled
resolution predicate, while this theorem preserves the finite `Fin`-indexed exact sequence for
module-theoretic computations. -/
@[stacks 0CXE "finite-projective resolution forgets to a coordinate projective resolution"]
theorem HasResolutionLE.toCoordinate
    {M : ModuleCat.{v} R} {d : ℕ} (hM : HasResolutionLE M d) :
    CategoryTheory.ModuleCat.ProjectiveResolution.Coordinate.HasLengthLE M d := sorry

/-- A finite-projective resolution gives the corresponding projective-dimension bound directly.

This is the consumer-facing finite-term analogue of `HasResolutionLE.hasLengthLE`; users should
not need to route through the coordinate presentation merely to recover the bound. -/
@[stacks 0CXE "projective dimension from a finite-projective resolution"]
theorem HasResolutionLE.hasProjectiveDimensionLE
    {M : ModuleCat.{v} R} {d : ℕ} (hM : HasResolutionLE M d) :
    HasProjectiveDimensionLE M d := sorry

/-- A projective resolution with finite terms truncates to a finite-projective resolution once its
`d`th canonical syzygy is projective.

The Noetherian and finite-module hypotheses are exactly what make the kernel terms finite.  The
canonical syzygy is the primary input; consumers that work with literal `ModuleCat` kernels can
transport their hypothesis through `kernelSyzygy.projective_iff` before calling this theorem. -/
@[stacks 0CXE "finite-projective resolution from a projective canonical syzygy"]
theorem HasResolutionLE.of_projectiveSyzygy
    {M : ModuleCat.{v} R} (P : CategoryTheory.ProjectiveResolution M) {d : ℕ}
    [IsNoetherianRing R] [Module.Finite R M]
    (hfinite : ∀ n, n < d → Module.Finite R (P.complex.X n))
    (hP : Projective (P.syzygy d)) :
    HasResolutionLE M d := sorry

/-- A finite module over a Noetherian ring has a finite-projective resolution of any given
projective-dimension bound.

The construction obtains a finite free resolution and truncates it at the projective canonical
syzygy.  No ambient `HasProjectiveResolution` instance is required, because the finite free
resolution is constructed explicitly. -/
@[stacks 0CXE "finite-projective resolution from projective dimension"]
theorem HasResolutionLE.of_hasProjectiveDimensionLE
    {M : ModuleCat.{v} R} [IsNoetherianRing R] [Module.Finite R M]
    {d : ℕ} (hM : HasProjectiveDimensionLE M d) :
    HasResolutionLE M d := sorry

/-- For a finite module over a Noetherian ring, a projective-dimension bound is equivalent to a
bounded resolution by finite-projective modules.

This is the direct consumer bridge. It packages the two directional construction theorems so
callers do not need to reconstruct the equivalence from a resolution witness. -/
@[stacks 0CXE "finite-projective resolution and projective dimension"]
theorem hasProjectiveDimensionLE_iff_hasResolutionLE
    {M : ModuleCat.{v} R} [IsNoetherianRing R] [Module.Finite R M] (d : ℕ) :
    HasProjectiveDimensionLE M d ↔ HasResolutionLE M d := sorry

/-- A positive-length finite-projective resolution begins with a finite-projective presentation
whose kernel has the remaining shorter finite-projective resolution.

The presenting term stays bundled in the finite-projective full subcategory, matching the term
owner used by the resolution itself. -/
@[stacks 0CXE "finite-projective resolution presentation"]
theorem HasResolutionLE.exists_presentation
    {M : ModuleCat.{v} R} {n : ℕ} (hM : HasResolutionLE M (n + 1)) :
    ∃ (P : ModuleCat.FiniteProjective.{u, v} R) (π : P.obj ⟶ M),
      Function.Surjective π.hom ∧
        HasResolutionLE (ModuleCat.of R (LinearMap.ker π.hom)) n := sorry

/-- A finite-projective presentation of `M` extends a finite-projective resolution of its kernel
by one step.

The finite and projective hypotheses on the presenting object are kept together as
`Module.FiniteProjective`; this is the natural raw-module input when the object has not already
been bundled in `ModuleCat.FiniteProjective R`. -/
@[stacks 0CXE "successor construction for a finite-projective resolution"]
theorem HasResolutionLE.succ_of_presentation
    {M P : ModuleCat.{v} R} (π : P ⟶ M) (hP : Module.FiniteProjective R P)
    (hπ : Function.Surjective π.hom) {n : ℕ}
    (hker : HasResolutionLE (ModuleCat.of R (LinearMap.ker π.hom)) n) :
    HasResolutionLE M (n + 1) := sorry

/-- The successor finite-projective-resolution predicate is exactly the presentation recurrence.

Together with HasResolutionLE.exists_presentation, this is the recursive interface for
constructing or consuming a finite-projective resolution without unfolding coordinate data. -/
@[stacks 0CXE "finite-projective resolution successor recurrence"]
theorem HasResolutionLE.succ_iff
    (M : ModuleCat.{v} R) (n : ℕ) :
    HasResolutionLE M (n + 1) ↔
      ∃ (P : ModuleCat.FiniteProjective.{u, v} R) (π : P.obj ⟶ M),
        Function.Surjective π.hom ∧
          HasResolutionLE (ModuleCat.of R (LinearMap.ker π.hom)) n := sorry

/-- An exact finite prefix of finite-projective modules, whose top kernel is finite projective,
is a finite-projective resolution of its target.

This coordinate form accepts the original exact sequence directly.  It avoids forcing callers to
transport every term and differential through the full subcategory before applying the bounded
resolution API. -/
@[stacks 0CXE "finite-projective resolution from an exact prefix"]
theorem HasResolutionLE.of_exact_topKernel
    {e : ℕ} {M : ModuleCat.{v} R} {F : Fin (e + 2) → ModuleCat.{v} R}
    (hF : ∀ i, Module.FiniteProjective R (F i))
    (δ : (i : Fin (e + 1)) → F i.succ ⟶ F i.castSucc) (π : F 0 ⟶ M)
    (hπ : Function.Surjective π.hom)
    (hExact₀ : Function.Exact (δ 0).hom π.hom)
    (hExact : ∀ i : Fin e, Function.Exact (δ i.succ).hom (δ i.castSucc).hom)
    (htop : Module.FiniteProjective R
      (ModuleCat.of R (LinearMap.ker (δ (Fin.last e)).hom))) :
    HasResolutionLE M (e + 2) := sorry

end FiniteProjective

/-- Compatibility name for `FiniteProjective.HasResolutionLE`. New code should use the
namespace-first owner. -/
@[stacks 0CXE "finite-projective resolution compatibility view"]
abbrev HasFinProjResLE
    (M : ModuleCat.{v} R) (d : ℕ) : Prop :=
  FiniteProjective.HasResolutionLE M d

/-- In length zero, the compatibility view keeps the projective-first conjunction used by existing
chapter consumers. -/
@[stacks 0CXE "finite-projective resolution at length zero"]
theorem hasFinProjResLE_zero_iff
    (M : ModuleCat.{v} R) :
    HasFinProjResLE M 0 ↔
      Module.Projective R M ∧ Module.Finite R M := sorry

/-- The canonical finite-projective length-zero view through the compatibility name. -/
@[stacks 0CXE "finite-projective resolution at canonical length zero"]
theorem HasFinProjResLE.zero_iff
    (M : ModuleCat.{v} R) :
    HasFinProjResLE M 0 ↔ Module.FiniteProjective R M := sorry

/-- The categorical bounded-resolution bridge through the compatibility name. -/
@[stacks 0CXE "finite-projective resolution forgets to a bounded projective resolution"]
theorem HasFinProjResLE.hasLengthLE
    {M : ModuleCat.{v} R} {d : ℕ} (hM : HasFinProjResLE M d) :
    CategoryTheory.ProjectiveResolution.HasLengthLE M d := sorry

end CategoryTheory.ModuleCat
