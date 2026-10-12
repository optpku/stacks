/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.ExteriorPower.Exact
public import ReasLib.LinearAlgebra.TensorPower.Symmetric.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import StacksCheckRecall

@[expose] public section

/-!
# Exact power sequences
@stack 00DO

The generic exactness theorems for symmetric and exterior powers are owned by
their respective ReasLib leaves. This file only translates the short-exact
sequence of `ModuleCat R` in the source item to those linear-algebra APIs.
-/

/- Lemma 10.13.2: a short exact sequence induces exact symmetric- and exterior-power
sequences, whose terminal maps remain surjective. -/
@[stacks 00DO "short-exact sequence bridge"]
#check @CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact

@[stacks 00DO "(1), symmetric-power exactness"]
#check @SymmetricPower.exact_leftTensorMap_map

@[stacks 00DO "(1), symmetric-power terminal surjectivity"]
#check @SymmetricPower.map_surjective

@[stacks 00DO "(2), exterior-power exactness"]
#check @exteriorPower.exact_leftTensorMap_map

@[stacks 00DO "(2), exterior-power terminal surjectivity"]
#check @exteriorPower.map_surjective
