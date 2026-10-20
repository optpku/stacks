/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution.Bounded
public import ReasLib.Algebra.Category.ModuleCat.ProjectiveResolution.Bounded
public import ReasLib.CategoryTheory.Abelian.Projective.Resolution.Syzygy

/-!
# Bounded free resolutions as projective resolutions

This leaf supplies the categorical view of bounded free resolutions. It depends on the canonical
projective-resolution boundedness owner, while the converse constructions requiring local-ring or
finiteness hypotheses remain in commutative-algebra applications.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ChainComplex.FreeResolution

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Forgetting freeness turns a bounded free resolution into a bounded categorical projective
resolution of the same module and length. -/
@[stacks 0CXD "bounded free resolution as projective resolution"]
theorem HasLengthLE.toProjectiveResolution
    {d : ℕ} (hM : HasLengthLE R M d) :
    CategoryTheory.ProjectiveResolution.HasLengthLE (ModuleCat.of R M) d := sorry

/-- Forgetting freeness gives the coordinate bounded projective-resolution presentation of the
same module and length. -/
@[stacks 0CXD "bounded free resolution as a coordinate projective resolution"]
theorem HasLengthLE.toCoordinate
    {d : ℕ} (hM : HasLengthLE R M d) :
    CategoryTheory.ModuleCat.ProjectiveResolution.Coordinate.HasLengthLE (ModuleCat.of R M) d := sorry

/-- A bounded free resolution gives the corresponding projective-dimension bound.

The conclusion is obtained through the canonical bounded projective-resolution owner and therefore
does not require a global choice of projective resolutions. -/
@[stacks 0CXD "projective dimension from a bounded free resolution"]
theorem HasLengthLE.hasProjectiveDimensionLE
    {d : ℕ} (hM : HasLengthLE R M d) :
    HasProjectiveDimensionLE (ModuleCat.of R M) d := sorry

end ChainComplex.FreeResolution

namespace CategoryTheory.ProjectiveResolution

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A chosen categorical projective resolution with free terms gives the corresponding raw free
resolution bound.  The termwise freeness is an explicit hypothesis, so this transport does not
need a universe-wide `Small` bridge or a temporary instance. -/
@[stacks 0CXD "free resolution from a chosen projective resolution"]
theorem HasLengthLE.toFreeResolution
    (P : ProjectiveResolution (ModuleCat.of R M)) {d : ℕ}
    (hbound : P.IsBoundedLE d)
    (hfree : ∀ n, Module.Free R (P.complex.X n)) :
    ChainComplex.FreeResolution.HasLengthLE R M d := sorry

/-- A chosen categorical projective resolution with finite free terms gives the corresponding raw
finite-free resolution bound. -/
@[stacks 0CXD "finite free resolution from a chosen projective resolution"]
theorem HasLengthLE.toFiniteFreeResolution
    (P : ProjectiveResolution (ModuleCat.of R M)) {d : ℕ}
    (hbound : P.IsBoundedLE d)
    (hfree : ∀ n, Module.Free R (P.complex.X n))
    (hfinite : ∀ n, Module.Finite R (P.complex.X n)) :
    ChainComplex.FiniteFreeResolution.HasLengthLE R M d := sorry

end CategoryTheory.ProjectiveResolution

namespace ChainComplex.FiniteFreeResolution

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A bounded finite free resolution gives the corresponding projective-dimension bound after
forgetting termwise finiteness. -/
@[stacks 0CXD "projective dimension from a bounded finite free resolution"]
theorem HasLengthLE.hasProjectiveDimensionLE
    {d : ℕ} (hM : HasLengthLE R M d) :
    HasProjectiveDimensionLE (ModuleCat.of R M) d := sorry

end ChainComplex.FiniteFreeResolution
