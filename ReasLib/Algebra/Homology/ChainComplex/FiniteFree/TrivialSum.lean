/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FiniteFree
public import ReasLib.Algebra.Homology.ChainComplex.TrivialSum
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite sums of trivial finite free complexes

This is the finite-free specialization of `ChainComplex.trivialSums`.  It
accepts arbitrary bundled finite-free modules, without choosing coordinates.
Coordinate models of disks belong in `FiniteFree.IdentityDisk`.
-/

@[expose] public section

open CategoryTheory ChainComplex

universe u

namespace FiniteFreeComplex

variable {R : Type u} [Ring R]

/-- A chain complex of `R`-modules is a trivial finite free sum if it lies in
the finite-coproduct-and-isomorphism closure of degree-zero singles and
identity disks on arbitrary finite-free modules. -/
@[stacks 00MY "trivial finite free sums"]
abbrev IsTrivialSum : ObjectProperty (ChainComplex (ModuleCat R) ℕ) :=
  ChainComplex.trivialSums (ModuleCat.finiteFree R)

namespace IsTrivialSum

/-- Any finite-free module placed in degree zero is a trivial finite free sum. -/
@[stacks 00MY "degree-zero trivial finite free sum"]
theorem single {M : ModuleCat R} (hM : ModuleCat.finiteFree R M) :
    IsTrivialSum ((ChainComplex.single₀ (ModuleCat R)).obj M) :=
  ChainComplex.trivialSums.single hM

/-- Any identity disk on a finite-free module is a trivial finite free sum. -/
@[stacks 00MY "identity-disk trivial finite free sum"]
theorem disk (i : ℕ) {M : ModuleCat R} (hM : ModuleCat.finiteFree R M) :
    IsTrivialSum (ChainComplex.disk M i) :=
  ChainComplex.trivialSums.disk i hM

/-- The standard rank-`n` free module placed in degree zero is a trivial
finite free sum. -/
@[stacks 00MY "standard degree-zero trivial finite free sum"]
theorem single_fin (n : ℕ) :
    IsTrivialSum
      ((ChainComplex.single₀ (ModuleCat R)).obj
        (ModuleCat.of R (Fin n → R))) :=
  single ⟨inferInstance, inferInstance⟩

/-- The identity disk on the standard rank-`n` free module is a trivial
finite free sum. -/
@[stacks 00MY "standard identity-disk trivial finite free sum"]
theorem disk_fin (i n : ℕ) :
    IsTrivialSum (ChainComplex.disk (ModuleCat.of R (Fin n → R)) i) :=
  disk i ⟨inferInstance, inferInstance⟩

end IsTrivialSum

end FiniteFreeComplex
