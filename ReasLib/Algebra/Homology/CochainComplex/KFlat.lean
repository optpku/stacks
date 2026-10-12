/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.Relative
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat.ModuleCat
public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat cochain complexes

@stack 06XZ

This file exposes the cochain-complex compatibility predicates and specializations of the
shape-general notion in `HomologicalComplex.KFlat`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace CochainComplex

section

variable {R : Type u} [CommRing R]

/-- A cochain complex of `R`-modules is termwise flat if each module `K^n` is flat. -/
@[stacks 064K "cochain-module compatibility predicate"]
def IsTermwiseFlat (K : CochainComplex (ModuleCat R) ℤ) : Prop :=
  ∀ n : ℤ, Module.Flat R (K.X n : Type u)

/-- The algebraic degreewise-flat predicate for cochain complexes agrees with the canonical
categorical termwise-flat predicate. -/
@[stacks 064K "cochain-module compatibility bridge"]
theorem isTermwiseFlat_iff_categorical
    (K : CochainComplex (ModuleCat R) ℤ) :
    CochainComplex.IsTermwiseFlat K ↔ HomologicalComplex.IsTermwiseFlat K := sorry

end

end CochainComplex

namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- A cochain complex is K-flat if totalized tensoring with it preserves acyclic cochain
complexes. -/
@[stacks 06XZ "cochain-complex form"]
abbrev IsKFlat (K : CochainComplex C ℤ) : Prop :=
  HomologicalComplex.IsKFlat K

/-- A K-flat cochain complex sends each acyclic input complex to an acyclic tensor
totalization. -/
lemma acyclic_tensorObj_of_isKFlat {K : CochainComplex C ℤ} (hK : K.IsKFlat)
    {M : CochainComplex C ℤ} [HomologicalComplex.HasTensor M K]
    (hM : M.Acyclic) :
    (HomologicalComplex.tensorObj M K).Acyclic := sorry

/-- A cochain complex is K-flat exactly when totalized tensoring with it preserves acyclic
cochain complexes. -/
theorem isKFlat_iff (K : CochainComplex C ℤ) :
    K.IsKFlat ↔
      ∀ ⦃M : CochainComplex C ℤ⦄
        [HomologicalComplex.HasTensor M K], M.Acyclic →
        (HomologicalComplex.tensorObj M K).Acyclic := sorry

end


end CochainComplex
