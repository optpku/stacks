module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Embedding.UpNat
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Commutative
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Nonnegative
public import ReasLib.RingTheory.Sequence.Koszul.Power
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integer chain-DGA models of powered Koszul complexes

The multiplicative Koszul complexes in `KoszulComplex.powerAlgebraSystem` are commutative monoid
objects in naturally indexed chain complexes. Extension by zero along
`ChainDGAlgebra.natEmbedding` followed by `ChainDGAlgebra.fromChainCommMon` turns them into an
integer-indexed chain-DGA tower while retaining the existing unit, multiplication, and transition
maps.

The exterior-algebra model supplies the additional odd-square-zero theorem needed for strict
graded commutativity over an arbitrary commutative ring. The exact-power family owns the stage
instance, which the reducible alias `power f n` inherits directly. Since `system` is an opaque
functor definition, a single named objectwise bridge exposes the same property to typeclass search
at `(system f).obj (op n)`; there is no duplicate instance for `power`. This leaf still stops before
divided powers: the operation `γ` is separate non-Prop data and is not manufactured from a
proposition.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe u

variable {R : Type u} [CommRing R]

namespace KoszulComplex.ChainDGA

/-- The integer-indexed chain DGA associated to the exact `n`th-power Koszul algebra. -/
@[stacks 0GZ4 "exact-power Koszul chain DGA"]
noncomputable abbrev pow {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    ChainDGAlgebra R :=
  (ChainDGAlgebra.fromChainCommMon R).obj (KoszulComplex.powAlgebra f n)

/-- The exterior-algebra multiplication makes every exact-power Koszul chain DGA strictly
graded-commutative, including odd-square-zero over an arbitrary commutative base ring. This is the
canonical instance owner for exact-power and zero-based stages. -/
@[stacks 0GZ4 "strict commutativity of powered Koszul chain DGAs",
  stacks 0GZ5 "strict commutativity of powered Koszul tower stages"]
instance powIsStrictlyCommutative {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (pow f n).IsStrictlyCommutative := sorry

/-- Every exact-power Koszul chain DGA is supported in nonnegative degrees. This is the
canonical instance owner for exact-power and zero-based stages. -/
@[stacks 0GZ4 "nonnegative support of powered Koszul chain DGAs",
  stacks 0GZ5 "nonnegative support of powered Koszul tower stages"]
instance powIsNonnegative {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (pow f n).IsNonnegative := sorry

/-- The exact-power multiplicative transition as an integer-indexed chain-DGA map. -/
@[stacks 0GZ4 "exact-power Koszul chain-DGA transition"]
noncomputable def powMap {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    pow f m ⟶ pow f n :=
  (ChainDGAlgebra.fromChainCommMon R).map (KoszulComplex.powAlgebraMap f h)

/-- The chain complex underlying an exact-power chain DGA is the corresponding Koszul complex
extended by zero to integer chain degrees. -/
@[simp]
theorem pow_toChainComplex {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (pow f n).toChainComplex =
      (KoszulComplex.powComplex f n).extend ChainDGAlgebra.natEmbedding := sorry

/-- Restricting an exact-power chain DGA back to natural degrees recovers its Koszul complex. -/
@[simp]
theorem pow_natRestriction {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (pow f n).natRestriction = KoszulComplex.powComplex f n := sorry

/-- The chain map underlying an exact-power DGA transition is extension by zero of the existing
Koszul transition. -/
@[simp]
theorem powMap_toChainMap {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (powMap f h).toChainMap =
      (ChainDGAlgebra.natEmbedding.extendFunctor (ModuleCat R)).map
        (KoszulComplex.powMap f h) := sorry

/-- The exact-power chain-DGA transition attached to reflexivity is the identity. -/
@[simp]
theorem powMap_refl {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    powMap f (le_refl n) = 𝟙 (pow f n) := sorry

/-- Exact-power chain-DGA transitions compose according to transitivity of exponent bounds. -/
theorem powMap_comp {ι : Type u} [Finite ι] (f : ι → R) {n m l : ℕ}
    (h_nm : n ≤ m) (h_ml : m ≤ l) :
    powMap f h_ml ≫ powMap f h_nm = powMap f (h_nm.trans h_ml) := sorry

namespace Reindex

/-- The integer-indexed chain-DGA isomorphism induced by a finite reindexing of the Koszul
generators.  It is the image of the commutative-algebra isomorphism owned by `Power`. -/
@[stacks 0GZ4 "reindexing isomorphism of exact-power Koszul chain DGAs"]
noncomputable def powIso {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    pow f n ≅ pow (fun j ↦ f (e.symm j)) n :=
  (ChainDGAlgebra.fromChainCommMon R).mapIso
    (KoszulComplex.Reindex.algebraIso f e n)

/-- The forward map of the DGA reindexing is the functor image of the algebra map. -/
@[simp]
theorem powIso_hom {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (powIso f e n).hom =
      (ChainDGAlgebra.fromChainCommMon R).map
        (KoszulComplex.Reindex.algebraHom f e n) := sorry

/-- The inverse map of the DGA reindexing is the functor image of the inverse algebra map. -/
@[simp]
theorem powIso_inv {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (powIso f e n).inv =
      (ChainDGAlgebra.fromChainCommMon R).map
        (KoszulComplex.Reindex.algebraInv f e n) := sorry

/-- The chain map underlying forward DGA reindexing is extension by zero of the powered Koszul
chain reindexing. -/
@[simp]
theorem powIso_hom_toChainMap {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (powIso f e n).hom.toChainMap =
      (ChainDGAlgebra.natEmbedding.extendFunctor (ModuleCat R)).map
        (KoszulComplex.Reindex.chainHom f e n) := sorry

/-- The chain map underlying inverse DGA reindexing is extension by zero of the inverse powered
Koszul chain reindexing. -/
@[simp]
theorem powIso_inv_toChainMap {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n : ℕ) :
    (powIso f e n).inv.toChainMap =
      (ChainDGAlgebra.natEmbedding.extendFunctor (ModuleCat R)).map
        (KoszulComplex.Reindex.chainInv f e n) := sorry

end Reindex

/-- Zero-based powered stage `n` is the integer chain DGA associated to exponent `n + 1`. -/
@[stacks 0GZ4 "zero-based powered Koszul chain DGA"]
noncomputable abbrev power {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    ChainDGAlgebra R :=
  (ChainDGAlgebra.fromChainCommMon R).obj (KoszulComplex.powerAlgebra f n)

/-- A zero-based powered chain-DGA stage is the corresponding exact-power stage. -/
@[simp]
theorem power_eq_pow {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    power f n = pow f (n + 1) := sorry

/-- The adjacent chain-DGA transition from zero-based powered stage `n + 1` to stage `n`. -/
@[stacks 0GZ4 "adjacent powered Koszul chain-DGA transition"]
noncomputable def step {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    power f (n + 1) ⟶ power f n :=
  (ChainDGAlgebra.fromChainCommMon R).map (KoszulComplex.powerAlgebraStep f n)

/-- The adjacent zero-based transition is the corresponding exact-power chain-DGA map. -/
theorem step_eq_powMap {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    step f n = powMap f (Nat.le_succ (n + 1)) := sorry

/-- The chain complex underlying a zero-based powered stage is the corresponding natural Koszul
complex extended by zero to integer chain degrees. -/
@[simp]
theorem power_toChainComplex {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (power f n).toChainComplex =
      (KoszulComplex.powerComplex f n).extend ChainDGAlgebra.natEmbedding := sorry

/-- Restricting a zero-based powered chain DGA to natural degrees recovers the existing powered
Koszul complex. -/
@[simp]
theorem power_natRestriction {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (power f n).natRestriction = KoszulComplex.powerComplex f n := sorry

/-- The underlying chain map of an adjacent DGA transition is extension by zero of the existing
powered Koszul step. -/
@[simp]
theorem step_toChainMap {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (step f n).toChainMap =
      (ChainDGAlgebra.natEmbedding.extendFunctor (ModuleCat R)).map
        (KoszulComplex.powerStep f n) := sorry

/-- The zero-based powered Koszul chain DGAs form a sequential inverse system by direct functor
composition from the existing multiplicative system. -/
@[stacks 0GZ4 "powered Koszul chain-DGA inverse system",
  stacks 0GZ5 "chain-DGA tower underlying powered Koszul--Tate comparison"]
noncomputable def system {ι : Type u} [Finite ι] (f : ι → R) :
    ℕᵒᵖ ⥤ ChainDGAlgebra R :=
  KoszulComplex.powerAlgebraSystem f ⋙ ChainDGAlgebra.fromChainCommMon R

/-- Every object of the powered Koszul chain-DGA system is strictly commutative. This is the
single bridge required because `system` is an opaque functor definition; zero-based stages use the
exact-power instance directly through the reducible abbreviation `power`. -/
@[stacks 0GZ5 "strict commutativity of powered Koszul tower objects"]
instance systemObjIsStrictlyCommutative {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    ((system f).obj (op n)).IsStrictlyCommutative := sorry

/-- Every object of the powered Koszul chain-DGA system is supported in nonnegative degrees.
This is the objectwise bridge required by the opaque system definition. -/
@[stacks 0GZ5 "nonnegative support of powered Koszul tower objects"]
instance systemObjIsNonnegative {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    ((system f).obj (op n)).IsNonnegative := sorry

/-- The object at index `n` of the powered chain-DGA system is zero-based powered stage `n`. -/
@[simp]
theorem system_obj {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (system f).obj (op n) = power f n := sorry

/-- The integer chain complex at index `n` is extension by zero of powered Koszul stage `n`. -/
@[simp]
theorem system_obj_toChainComplex {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    ((system f).obj (op n)).toChainComplex =
      (KoszulComplex.powerComplex f n).extend ChainDGAlgebra.natEmbedding := sorry

/-- The generating transition of the powered chain-DGA system is `step`. -/
theorem system_map_succ {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (system f).map (homOfLE (Nat.le_add_right n 1)).op = step f n := sorry

/-- An arbitrary powered chain-DGA transition is the corresponding exact-power transition. -/
@[stacks 0GZ5 "arbitrary transition in the powered Koszul chain-DGA system"]
theorem system_map {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (system f).map (homOfLE h).op =
      powMap f (Nat.add_le_add_right h 1) := sorry

/-- The chain map underlying an arbitrary system transition is extension by zero of the existing
exact-power Koszul transition. -/
@[stacks 0GZ5 "underlying map of a powered Koszul chain-DGA transition"]
theorem system_map_toChainMap
    {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    ((system f).map (homOfLE h).op).toChainMap =
      (ChainDGAlgebra.natEmbedding.extendFunctor (ModuleCat R)).map
        (KoszulComplex.powMap f (Nat.add_le_add_right h 1)) := sorry

/-- Restricting the powered integer chain-DGA system to natural degrees recovers the existing
powered Koszul chain-complex system. -/
@[stacks 0GZ5 "natural restriction of the powered Koszul chain-DGA system"]
theorem system_comp_natRestriction {ι : Type u} [Finite ι] (f : ι → R) :
    system f ⋙ ChainDGAlgebra.natRestrictionFunctor R =
      KoszulComplex.powerSystem f := sorry

section StrictCommutativityInference

variable {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ)

-- These checks guard the intentional instance design: exact and zero-based stages share one
-- owner, while the opaque system has precisely the objectwise bridge needed by typeclass search.
#synth (pow f n).IsStrictlyCommutative
#synth (power f n).IsStrictlyCommutative
#synth ((system f).obj (op n)).IsStrictlyCommutative
#synth (pow f n).IsNonnegative
#synth (power f n).IsNonnegative
#synth ((system f).obj (op n)).IsNonnegative

end StrictCommutativityInference

-- All object and morphism data are explicit functor images of the existing Koszul monoids and
-- transitions. Any `sorryAx` dependency is confined to proposition-valued bridge statements and
-- inherited monoidal/DGA law fields.

end KoszulComplex.ChainDGA
