/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ChainComplex.ModuleSingle
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise

/-!
# Free Resolutions of Modules

This file owns the chain-complex predicates for free and finite free resolutions of modules.
The more primitive termwise finiteness predicates live in
`ReasLib.Algebra.Homology.HomologicalComplex.Termwise` and apply to arbitrary complex shapes.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ChainComplex

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {F : ChainComplex (ModuleCat R) ℕ}

/-- Definition 10.71.2 (2): a free resolution of an `R`-module `M` is an augmentation to
`moduleSingle R M` that is a quasi-isomorphism and whose chain-complex terms are free. -/
@[stacks 00LQ]
class IsFreeResolution (π : F ⟶ moduleSingle R M) : Prop extends QuasiIso π where
  /-- The resolving chain complex is termwise free. -/
  termwise_free : IsTermwiseFree F

namespace IsFreeResolution

/-- The augmentation of a free resolution is a quasi-isomorphism. -/
@[stacks 00LQ "free resolution quasi-isomorphism"]
theorem quasiIso (π : F ⟶ moduleSingle R M) [h : IsFreeResolution π] : QuasiIso π := sorry

/-- The resolving complex of a free resolution is termwise free. -/
@[stacks 00LQ "free resolution termwise freeness"]
theorem termwiseFree (π : F ⟶ moduleSingle R M) [h : IsFreeResolution π] :
    IsTermwiseFree F := sorry

/-- A free resolution has a free module in every chain degree. -/
@[stacks 00LQ "free resolution free term"]
theorem free (π : F ⟶ moduleSingle R M) [h : IsFreeResolution π] (n : ℕ) :
    Module.Free R (F.X n) := sorry

/-- Every component of the resolving complex of a free resolution is projective. -/
@[stacks 00LQ "free resolution projective term"]
theorem projective (π : F ⟶ moduleSingle R M) [h : IsFreeResolution π] (n : ℕ) :
    Projective (F.X n) := sorry

/-- A free resolution gives the standard mathlib projective resolution of its target module. -/
@[stacks 00LQ "free resolution to projective resolution"]
noncomputable def toProjectiveResolution (π : F ⟶ moduleSingle R M) [h : IsFreeResolution π] :
    ProjectiveResolution (ModuleCat.of R M) where
  complex := F
  projective n := projective π n
  π := π
  quasiIso := quasiIso π

/-- The complex underlying the projective resolution associated to a free resolution is the
original resolving complex. -/
@[simp, stacks 00LQ "projective resolution underlying complex"]
theorem toProjectiveResolution_complex (π : F ⟶ moduleSingle R M) [IsFreeResolution π] :
    (toProjectiveResolution π).complex = F := sorry

/-- The augmentation of the projective resolution associated to a free resolution is the original
augmentation. -/
@[simp, stacks 00LQ "projective resolution augmentation"]
theorem toProjectiveResolution_π (π : F ⟶ moduleSingle R M) [IsFreeResolution π] :
    (toProjectiveResolution π).π = π := sorry

end IsFreeResolution

/-- A free-resolution predicate is precisely a quasi-isomorphism together with termwise
freeness of the resolving chain complex. -/
@[stacks 00LQ "free resolution characterization"]
theorem isFreeResolution_iff (π : F ⟶ moduleSingle R M) :
    IsFreeResolution π ↔ QuasiIso π ∧ IsTermwiseFree F := sorry

/-- Definition 10.71.2 (3): a finite free resolution is a free resolution whose terms are also
finite `R`-modules. -/
@[stacks 00LQ]
class IsFiniteFreeResolution (π : F ⟶ moduleSingle R M) : Prop extends IsFreeResolution π where
  /-- The resolving chain complex is termwise finite. -/
  termwise_finite : IsTermwiseFinite F

namespace IsFiniteFreeResolution

/-- The resolving complex of a finite free resolution is termwise finite. -/
@[stacks 00LQ "finite free resolution termwise finiteness"]
theorem termwiseFinite (π : F ⟶ moduleSingle R M) [h : IsFiniteFreeResolution π] :
    IsTermwiseFinite F := sorry

/-- A finite free resolution has a finite module in every chain degree. -/
@[stacks 00LQ "finite free resolution finite term"]
theorem finite (π : F ⟶ moduleSingle R M) [h : IsFiniteFreeResolution π] (n : ℕ) :
    Module.Finite R (F.X n) := sorry

/-- A finite free resolution has a free module in every chain degree. -/
@[stacks 00LQ "finite free resolution free term"]
theorem free (π : F ⟶ moduleSingle R M) [IsFiniteFreeResolution π] (n : ℕ) :
    Module.Free R (F.X n) := sorry

end IsFiniteFreeResolution

/-- A finite-free-resolution predicate is a free-resolution predicate together with termwise
finiteness. -/
@[stacks 00LQ "finite free resolution characterization"]
theorem isFiniteFreeResolution_iff (π : F ⟶ moduleSingle R M) :
    IsFiniteFreeResolution π ↔ IsFreeResolution π ∧ IsTermwiseFinite F := sorry

/-- Lemma 10.71.1 (1), tag `00LP`: every module admits a resolution by free modules. -/
@[stacks 00LP "free resolutions"]
theorem exists_freeResolution :
    ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle R M),
      IsFreeResolution π := sorry

/-- Lemma 10.71.1 (2), tag `00LP`: a finite module over a Noetherian ring admits a resolution
by finite free modules. -/
@[stacks 00LP "finite free resolutions"]
theorem exists_finiteFreeResolution [IsNoetherianRing R] [Module.Finite R M] :
    ∃ (F : ChainComplex (ModuleCat R) ℕ) (π : F ⟶ moduleSingle R M),
      IsFiniteFreeResolution π := sorry

end ChainComplex
