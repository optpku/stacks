/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pro.Sequential.Interleaving
public import ReasLib.RingTheory.Sequence.Koszul.Tate
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pro-systems of powered Koszul--Tate approximations

A Koszul--Tate tower chooses exact exponents `n i = index i + 1`, beginning at `1`, and an
explicit `Tate.Approximation` between consecutive selected Koszul stages.  Its intermediate
algebras form an inverse system with transition
`A(i + 1) ⟶ K(n(i + 1)) ⟶ A(i)`.  The two rows of comparison maps assemble into natural
transformations and a `Pro.SequentialFactorization`, hence into mutually inverse sequential
pro-morphism representatives.

The tower and every map are explicit data.  No definition chooses a divided-power system or a
Tate approximation from a deferred existence theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open CategoryTheory.SequentialInverseSystem

universe u x

variable {R : Type u} [CommRing R]

namespace KoszulComplex.Tate

open KoszulComplex.DP

variable {ι : Type u} [Finite ι] {f : ι → R}

/-- The positive exact exponent represented by a zero-based stage index. -/
@[stacks 0GZ5 "positive exponent selected by a zero-based tower index"]
def exactExponent (index : ℕ →o ℕ) (i : ℕ) : ℕ+ :=
  ⟨index i + 1, Nat.succ_pos _⟩

/-- Remark 23.12.2 (Tag 0GZ5): a coherent tower of powered Koszul--Tate approximations.

The stored index is zero-based so that it addresses `K.system` directly.  The source exponent is
`exactExponent index i`; consequently `index_zero` expresses `n₀ = 1` without subtraction. -/
@[stacks 0GZ5 "powered Koszul--Tate approximation tower"]
structure Tower (K : System f) where
  /-- The selected zero-based stages of the powered Koszul inverse system. -/
  index : ℕ →o ℕ
  /-- The first selected zero-based stage is `0`, equivalently the first exact exponent is `1`. -/
  index_zero : index 0 = 0
  /-- The selected stages are strictly increasing. -/
  index_strictMono : StrictMono index
  /-- The approximation whose target exponent is `exactExponent index i`. -/
  approximation (i : ℕ) : Approximation.{u, x} K (exactExponent index i)
  /-- The later exponent of the `i`th approximation is the next selected exact exponent. -/
  next (i : ℕ) : (approximation i).N = exactExponent index (i + 1)

namespace Tower

variable {K : System f}

/-- The positive exact exponent `n_i` selected by a Koszul--Tate tower. -/
@[stacks 0GZ5 "exact exponent in a Koszul--Tate tower"]
abbrev exponent (T : Tower K) (i : ℕ) : ℕ+ :=
  exactExponent T.index i

/-- The exact exponent sequence starts at `n₀ = 1`. -/
@[simp]
theorem exponent_zero (T : Tower K) : T.exponent 0 = 1 := sorry

/-- The exact exponent sequence is strictly increasing. -/
theorem exponent_strictMono (T : Tower K) : StrictMono T.exponent := sorry

/-- Every original zero-based stage lies below the selected stage with the same index. -/
theorem le_index (T : Tower K) (i : ℕ) : i ≤ T.index i := sorry

/-- The intermediate divided-power chain DGA `A_(i+1)` in the tower. -/
@[stacks 0GZ5 "intermediate Tate stage in a Koszul--Tate tower"]
abbrev stage (T : Tower K) (i : ℕ) : DividedPowerChainAlgebra R :=
  (T.approximation i).resolution.algebra

/-- The vertical comparison `K_(n_(i+1)) ⟶ A_(i+1)`. -/
@[stacks 0GZ5 "Koszul-to-Tate comparison map in a tower"]
def fromKoszul (T : Tower K) (i : ℕ) :
    K.system.obj (op (T.index (i + 1))) ⟶ T.stage i :=
  eqToHom (congrArg K.stage (congrArg Subtype.val (T.next i).symm)) ≫
    (T.approximation i).fromKoszul

/-- The vertical comparison `A_(i+1) ⟶ K_(n_i)`. -/
@[stacks 0GZ5 "Tate-to-Koszul comparison map in a tower"]
def toKoszul (T : Tower K) (i : ℕ) :
    T.stage i ⟶ K.system.obj (op (T.index i)) :=
  (T.approximation i).toKoszul

/-- The transition `A_(i+2) ⟶ A_(i+1)` is the source composite through `K_(n_(i+1))`. -/
@[stacks 0GZ5 "transition between intermediate Tate stages"]
def step (T : Tower K) (i : ℕ) : T.stage (i + 1) ⟶ T.stage i :=
  T.toKoszul (i + 1) ≫ T.fromKoszul i

/-- The intermediate algebras and their explicit Koszul-factorized transitions form a sequential
inverse system. -/
@[stacks 0GZ5 "Koszul--Tate inverse system"]
def system (T : Tower K) : ℕᵒᵖ ⥤ DividedPowerChainAlgebra R :=
  CategoryTheory.Pro.SequentialFactorization.ofStagesSystem
    K.system T.index T.stage T.fromKoszul T.toKoszul

/-- Object `i` of the Koszul--Tate inverse system is the `i`th intermediate algebra. -/
@[simp, stacks 0GZ5 "object of the Koszul--Tate inverse system"]
theorem system_obj (T : Tower K) (i : ℕ) :
    T.system.obj (op i) = T.stage i := sorry

/-- The generating transition of the Koszul--Tate inverse system is
`A_(i+2) ⟶ K_(n_(i+1)) ⟶ A_(i+1)`. -/
@[stacks 0GZ5 "transition in the Koszul--Tate inverse system"]
theorem system_stepMap (T : Tower K) (i : ℕ) :
    stepMap T.system i = T.toKoszul (i + 1) ≫ T.fromKoszul i := sorry

/-- Each selected Koszul transition factors through its intermediate Tate algebra. -/
@[stacks 0GZ5 "Koszul transition through a Tate approximation"]
theorem fromKoszul_toKoszul (T : Tower K) (i : ℕ) :
    T.fromKoszul i ≫ T.toKoszul i =
      transitionMap K.system
        (T.index.monotone (Nat.le_add_right i 1)) := sorry

/-- The selected Koszul stages and intermediate Tate stages define a coherent sequential
factorization. -/
@[stacks 0GZ5 "Koszul--Tate sequential factorization"]
def factorization (T : Tower K) :
    CategoryTheory.Pro.SequentialFactorization K.system T.system :=
  CategoryTheory.Pro.SequentialFactorization.ofStages K.system T.index T.le_index T.stage
    T.fromKoszul T.toKoszul T.fromKoszul_toKoszul

/-- The factorization uses the selected zero-based exponent indices. -/
@[simp, stacks 0GZ5 "reindexing of the Koszul--Tate sequential factorization"]
theorem factorization_reindex (T : Tower K) :
    T.factorization.reindex = T.index := sorry

/-- The upper squares of the three-row Koszul--Tate diagram commute. -/
@[stacks 0GZ5 "upper commutative square in the Koszul--Tate tower"]
theorem top_commutes (T : Tower K) (i : ℕ) :
    transitionMap K.system
          (T.index.monotone (Nat.add_le_add_right (Nat.le_add_right i 1) 1)) ≫
        T.fromKoszul i =
      T.fromKoszul (i + 1) ≫ stepMap T.system i := sorry

/-- The lower squares of the three-row Koszul--Tate diagram commute. -/
@[stacks 0GZ5 "lower commutative square in the Koszul--Tate tower"]
theorem bottom_commutes (T : Tower K) (i : ℕ) :
    stepMap T.system i ≫ T.toKoszul i =
      T.toKoszul (i + 1) ≫
        transitionMap K.system
          (T.index.monotone (Nat.le_add_right i 1)) := sorry

/-- The upper vertical arrows form a natural transformation from the next selected Koszul
subsystem to the Tate system. -/
@[stacks 0GZ5 "Koszul-to-Tate comparison natural transformation"]
def fromKoszulNatTrans (T : Tower K) :
    T.factorization.homReindex.toFunctor.op ⋙ K.system ⟶ T.system :=
  T.factorization.homNatTrans

/-- The lower vertical arrows form a natural transformation from the Tate system to the selected
Koszul subsystem. -/
@[stacks 0GZ5 "Tate-to-Koszul comparison natural transformation"]
def toKoszulNatTrans (T : Tower K) :
    T.system ⟶ T.index.toFunctor.op ⋙ K.system :=
  T.factorization.fromStageNatTrans

/-- A component of the upper comparison natural transformation is the supplied Koszul-to-Tate
map. -/
@[simp]
theorem fromKoszulNatTrans_app (T : Tower K) (i : ℕ) :
    T.fromKoszulNatTrans.app (op i) = T.fromKoszul i := sorry

/-- A component of the lower comparison natural transformation is the supplied Tate-to-Koszul
map. -/
@[simp]
theorem toKoszulNatTrans_app (T : Tower K) (i : ℕ) :
    T.toKoszulNatTrans.app (op i) = T.toKoszul i := sorry

/-- The sequential pro-morphism representative from the powered Koszul system to the Tate
system. -/
@[stacks 0GZ5 "Koszul-to-Tate sequential pro-comparison"]
def comparison (T : Tower K) : CategoryTheory.Pro.SequentialHom K.system T.system :=
  T.factorization.hom

/-- The sequential representative in the reverse direction. -/
@[stacks 0GZ5 "Tate-to-Koszul sequential pro-comparison"]
def comparisonInverse (T : Tower K) :
    CategoryTheory.Pro.SequentialHom T.system K.system :=
  T.factorization.inv

/-- The Koszul-to-Tate comparison has the explicit reverse representative as an inverse up to
common refinement. -/
@[stacks 0GZ5 "Koszul--Tate representative inverse"]
theorem comparison_hasRepresentativeInverse (T : Tower K) :
    T.comparison.HasRepresentativeInverse := sorry

/-- Remark 23.12.2 (Tag 0GZ5): the powered Koszul and Tate inverse systems are pro-isomorphic in
the category of divided-power chain DGAs. -/
@[stacks 0GZ5 "Koszul and Tate inverse systems are pro-isomorphic"]
theorem comparison_isIso (T : Tower K) :
    IsIso T.comparison.toHom :=
  T.factorization.hom_isIso

/-- Typeclass search can use the canonical pro-isomorphism of every explicit Koszul--Tate tower
without a proof-local `letI`. -/
@[stacks 0GZ5 "typeclass bridge for the Koszul--Tate pro-isomorphism"]
instance comparisonIsIso (T : Tower K) :
    IsIso T.comparison.toHom :=
  comparison_isIso T

/-- Over a Noetherian ring, the canonical powered Koszul divided-power system admits a coherent
Koszul--Tate tower.  This specialization avoids forcing downstream users to pass the canonical
system explicitly. -/
@[stacks 0GZ5 "canonical powered Koszul--Tate tower exists"]
theorem nonempty_canonical [IsNoetherianRing R] (f : ι → R) :
    Nonempty (Tower.{u, x} (KoszulComplex.DP.system f)) := sorry

end Tower

/-- Over a Noetherian ring, there exist an explicit compatible divided-power structure on the
powered Koszul system and a coherent Koszul--Tate tower over it. -/
@[stacks 0GZ5 "existence of a powered Koszul--Tate pro-system"]
theorem exists_system_tower [IsNoetherianRing R] (f : ι → R) :
    ∃ K : System f, Nonempty (Tower.{u, x} K) := sorry

end KoszulComplex.Tate
