/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ChainComplex.Bounded
public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Basic

/-!
# Finite free coordinates from termwise data

This leaf turns a bounded termwise finite-free chain complex into the explicit
`FiniteFreeComplex` coordinate owner.  The chosen `Fin` coordinates are made
once here, so resolution and matrix arguments do not repeat noncanonical
basis choices locally.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace FiniteFreeComplex

variable {R : Type u} [Ring R] [StrongRankCondition R]
variable {e : ℕ}

/-- Package a bounded termwise finite-free complex with the canonical finite-coordinate bases
coming from `Module.finBasis`. -/
@[stacks 00MS "finite-free complex from bounded termwise data"]
def ofBounded (F : ChainComplex (ModuleCat R) ℕ) [F.IsTermwiseFiniteFree]
    (hbound : ChainComplex.IsBoundedLE F e) : _root_.FiniteFreeComplex R e where
  toChainComplex := F
  isZero_toChainComplex_X := hbound
  rank i := Module.finrank R (F.X i)
  termIso i := (Module.finBasis R (F.X i)).equivFun.toModuleIso

namespace ofBounded

/-- The underlying chain complex of `FiniteFreeComplex.ofBounded` is the input complex. -/
@[simp, stacks 00MS "ofBounded underlying complex"]
theorem toChainComplex (F : ChainComplex (ModuleCat R) ℕ) [F.IsTermwiseFiniteFree]
    (hbound : ChainComplex.IsBoundedLE F e) :
    (FiniteFreeComplex.ofBounded F hbound).toChainComplex = F := sorry

/-- The displayed rank of `FiniteFreeComplex.ofBounded` is the module finrank in each retained
degree. -/
@[simp, stacks 00MS "ofBounded rank"]
theorem rank (F : ChainComplex (ModuleCat R) ℕ) [F.IsTermwiseFiniteFree]
    (hbound : ChainComplex.IsBoundedLE F e) (i : Fin (e + 1)) :
    (FiniteFreeComplex.ofBounded F hbound).rank i = Module.finrank R (F.X i) := sorry

/-- The terms above the bound remain zero after packaging by `FiniteFreeComplex.ofBounded`. -/
@[stacks 00MS "ofBounded zero terms above the bound"]
theorem isZero_X (F : ChainComplex (ModuleCat R) ℕ) [F.IsTermwiseFiniteFree]
    (hbound : ChainComplex.IsBoundedLE F e) {n : ℕ} (hn : e < n) :
    IsZero ((FiniteFreeComplex.ofBounded F hbound).toChainComplex.X n) := sorry

end ofBounded

end FiniteFreeComplex
