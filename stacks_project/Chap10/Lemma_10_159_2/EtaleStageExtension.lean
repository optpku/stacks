/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.RingTheory.Unramified.LocalRing
public import ReasLib.RingTheory.Polynomial.Local
public import ReasLib.RingTheory.LocalRing.AdjoinRoot
public import ReasLib.RingTheory.RingHom.IndEtale.Composition
public import ReasLib.RingTheory.RingHom.IndEtale.Colimit
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import stacks_project.Chap10.Lemma_10_159_1.ResidueExtensionStage
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory MorphismProperty
open CommRingCat
open IsLocalRing
open RingHom

universe u v w

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

variable (R)

/-- Helper for Chap10 Lemma 10 159 2: changing only the proof of the intermediate-field
inclusion in a stage morphism does not change its underlying algebra map. -/
theorem ResidueExtensionStage.Hom.toAlgHom_cast_le
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    {L M : IntermediateField (ResidueField R) K}
    {h h' : L ≤ M}
    {S : ResidueExtensionStage.{u, w, max u w} (R := R) K L}
    {T : ResidueExtensionStage.{u, w, max u w} (R := R) K M}
    (f : ResidueExtensionStage.Hom h S T) :
    (cast (by rw [Subsingleton.elim h h']) f :
        ResidueExtensionStage.Hom h' S T).toAlgHom = f.toAlgHom := sorry
/-- Helper for Lemma 10.159.2: once the source-faithful recursion has produced a top stage whose
structural map from `R` is ind-étale, the public theorem is only an unpacking step. -/
theorem exists_filteredColimitOfEtale_localAlgebra_with_residueField_equiv_of_top_stage
    (K : Type w) [Field K] [Algebra (ResidueField R) K]
    (hT :
      ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K
          (⊤ : IntermediateField (ResidueField R) K),
        Nonempty
          (ResidueExtensionStage.Hom
            (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊤ by simp)
            (ResidueExtensionStage.base (R := R) K) T) ∧
          RingHom.IndEtale.Raw.{u, max u w, max u w} (algebraMap R T.A)) :
    ∃ (R' : Type (max u w)) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R')
      (_ : IsLocalHom (algebraMap R R'))
      (e : ResidueField R' ≃ₐ[ResidueField R] K),
      RingHom.IndEtale.Raw.{u, max u w, max u w} (algebraMap R R') := sorry
/-- Helper for Lemma 10.159.2: after transporting the stage residue field to the current
intermediate field `L`, the one-element extension `L(x)` remains separable over the stage residue
field. -/
lemma adjoin_singleton_isSeparable_over_stage_residue
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K]
    {L : IntermediateField (ResidueField R) K}
    (S : ResidueExtensionStage (R := R) K L) (x : K) :
    let Lx : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx :=
      (IntermediateField.inclusion
        (ResidueExtensionStage.le_restrictScalars_adjoin_singleton (R := R) L x)).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    Algebra.IsSeparable (ResidueField S.A) Lx := sorry
/-- Helper for Lemma 10.159.2: the generator provided by `stage_adjoin_singleton_top` is integral
over the stage residue field when the ambient extension is algebraic. -/
lemma stage_adjoin_singleton_top_isIntegral_over_stage_residue
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsAlgebraic (ResidueField R) K]
    {L : IntermediateField (ResidueField R) K}
    (S : ResidueExtensionStage (R := R) K L) (x : K) :
    let Lx : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
    letI : Algebra (ResidueField S.A) L := S.residueEquiv.toRingHom.toAlgebra
    letI : Algebra L Lx :=
      (IntermediateField.inclusion
        (ResidueExtensionStage.le_restrictScalars_adjoin_singleton (R := R) L x)).toAlgebra
    letI : Algebra (ResidueField S.A) Lx :=
      RingHom.toAlgebra ((algebraMap L Lx).comp (algebraMap (ResidueField S.A) L))
    letI : IsScalarTower (ResidueField S.A) L Lx :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    ∃ α : Lx,
      IntermediateField.adjoin (ResidueField S.A) ({α} : Set Lx) = ⊤ ∧
        IsIntegral (ResidueField S.A) α := sorry
/-- Helper for Lemma 10.159.2: for a finite-presentation local map, flatness together with the
maximal-ideal equality and separable residue-field extension already gives global étaleness. -/
lemma etale_of_flat_local_extension_of_map_eq_maximalIdeal_of_separable_residue
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    [Algebra.FinitePresentation A B]
    (hflat : (algebraMap A B).Flat)
    (hmap : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    (algebraMap A B).Etale := sorry
/-- Helper for Lemma 10.159.2: adjoining one separable algebraic element to a stage preserves the
filtered-colimit-of-étale invariant on the ambient map from `R`. -/
lemma extend_stage_by_separable_element_with_filteredColimit
    {K : Type w} [Field K] [Algebra (ResidueField R) K]
    [Algebra.IsSeparable (ResidueField R) K]
    [Algebra.IsAlgebraic (ResidueField R) K]
    {L : IntermediateField (ResidueField R) K}
    (S : ResidueExtensionStage.{u, w, max u w} (R := R) K L)
    (hS : RingHom.IndEtale.Raw.{u, max u w, max u w} (algebraMap R S.A))
    (x : K) :
    let Lx : IntermediateField (ResidueField R) K :=
      (IntermediateField.adjoin L ({x} : Set K)).restrictScalars (ResidueField R)
    ∃ T : ResidueExtensionStage.{u, w, max u w} (R := R) K Lx,
      Nonempty
        (ResidueExtensionStage.Hom
          (ResidueExtensionStage.le_restrictScalars_adjoin_singleton (R := R) L x) S T) ∧
      RingHom.IndEtale.Raw.{u, max u w, max u w} (algebraMap R T.A) := sorry
/-- Helper for Lemma 10.159.2: the zero prefix stage already carries the ind-étale owner, because
the base map `R → R` is étale. -/
theorem exists_zero_prefix_stage_with_filteredColimit
    (K : Type w) [Field K] [Algebra (ResidueField R) K] :
    ∃ S : ResidueExtensionStage.{u, w, u} (R := R) K
        (⊥ : IntermediateField (ResidueField R) K),
      Nonempty
        (ResidueExtensionStage.Hom
          (show (⊥ : IntermediateField (ResidueField R) K) ≤ ⊥ by simp)
          (ResidueExtensionStage.base (R := R) K) S) ∧
      RingHom.IndEtale.Raw (algebraMap R S.A) := sorry
end
