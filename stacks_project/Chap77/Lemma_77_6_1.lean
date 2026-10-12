/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Defs.Filter
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Lemma 77.6.1

On a decent algebraic space locally of finite type over a scheme, a relatively
associated point of a finite-type quasi-coherent module that specializes into a
fibre along which the module is flat specializes to a relatively associated
point of that fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

namespace relativeAssassin

/-- Lemma 77.6.1: Let `S` be a scheme. Let `X` be a decent algebraic space
locally of finite type over `S`. Let `ℱ` be a finite type, quasi-coherent
`𝒪_X`-module. Let `s ∈ S` such that `ℱ` is flat over `S` at all points of
`|X_s|`. Let `x' ∈ Ass_{X/S}(ℱ)`. If the closure of `{x'}` in `|X|` meets
`|X_s|`, then the closure meets `Ass_{X/S}(ℱ) ∩ |X_s|`.
Here `Ass_{X/S}(ℱ)` is `relativeAssassin (toBase X) ℱ` and `|X_s|` is
`Points.base ⁻¹' {s}`. -/
@[stacks 0CW1]
theorem exists_mem_fiber_of_specializes {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [LocallyOfFiniteType (toBase X)] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S) {x' : Points X}
    (hx' : x' ∈ relativeAssassin (toBase X) ℱ)
    (hflat : ∀ z : Points X, Points.base z = s → flatOverAt ℱ (toBase X) z)
    (hmeets : ∃ t : Points X, Points.base t = s ∧ Specializes x' t) :
    ∃ x : Points X,
      Points.base x = s ∧ x ∈ relativeAssassin (toBase X) ℱ ∧ Specializes x' x :=
  sorry

/-- If the closure of `{x'}` meets the fibre `|X_s|`, then it meets
`Ass_{X/S}(ℱ) ∩ |X_s|`, under the same hypotheses as
`exists_mem_fiber_of_specializes`. -/
theorem exists_mem_fiber_of_closure_meets {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] [LocallyOfFiniteType (toBase X)] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S) {x' : Points X}
    (hx' : x' ∈ relativeAssassin (toBase X) ℱ)
    (hflat : ∀ z : Points X, Points.base z = s → flatOverAt ℱ (toBase X) z)
    (hmeets : (closure {x'} ∩ Points.base ⁻¹' {s}).Nonempty) :
    (closure {x'} ∩ relativeAssassin (toBase X) ℱ ∩ Points.base ⁻¹' {s}).Nonempty :=
  sorry

end relativeAssassin

end AlgebraicGeometry.AlgebraicSpace.Modules
