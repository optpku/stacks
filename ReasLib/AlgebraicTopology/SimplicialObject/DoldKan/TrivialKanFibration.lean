/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.KernelAcyclic
public import ReasLib.AlgebraicTopology.DoldKan.Equivalence
public import ReasLib.AlgebraicTopology.SimplicialObject.Grp.KanFibration
public import ReasLib.AlgebraicTopology.SimplicialObject.Underlying.TrivialKanFibration
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 08P1

# Dold--Kan criteria for trivial Kan fibrations

The normalized Moore and alternating-face complexes detect the same quasi-isomorphisms. For
simplicial abelian groups, a degreewise-surjective such map is a trivial Kan fibration after
forgetting to simplicial sets.
-/

@[expose] public section

open CategoryTheory.Limits Opposite
open AlgebraicTopology AlgebraicTopology.DoldKan
open SSet.modelCategoryQuillen

universe v u

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]

private theorem normalizedMoore_quasiIso_iff_alternatingFace
    {X Y : SimplicialObject A} (f : X ⟶ Y) :
    QuasiIso ((normalizedMooreComplex A).map f) ↔
      QuasiIso ((alternatingFaceMapComplex A).map f) := by
  haveI : QuasiIso (inclusionOfMooreComplexMap X) :=
    (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X)).quasiIso_hom
  haveI : QuasiIso (inclusionOfMooreComplexMap Y) :=
    (homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := Y)).quasiIso_hom
  have hcomm :
      (normalizedMooreComplex A).map f ≫ inclusionOfMooreComplexMap Y =
        inclusionOfMooreComplexMap X ≫ (alternatingFaceMapComplex A).map f :=
    (inclusionOfMooreComplex A).naturality f
  rw [← quasiIso_iff_comp_right
      ((normalizedMooreComplex A).map f) (inclusionOfMooreComplexMap Y),
    hcomm, quasiIso_iff_comp_left]

namespace AddCommGrp

variable {X Y : SimplicialObject AddCommGrpCat.{u}}

namespace underlying

namespace trivialKanFibrations

/-- Epimorphic normalized-Moore quasi-isomorphisms of simplicial abelian groups form a
subproperty of the underlying trivial Kan fibrations. -/
@[stacks 08P1 "normalized-Moore criterion for underlying trivial Kan fibrations"]
theorem normalizedMoore :
    (MorphismProperty.epimorphisms (SimplicialObject AddCommGrpCat.{u}) ⊓
      (HomologicalComplex.quasiIso AddCommGrpCat.{u} (ComplexShape.down ℕ)).inverseImage
        (normalizedMooreComplex AddCommGrpCat.{u})) ≤
      Underlying.trivialKanFibrations (forget AddCommGrpCat) := sorry

/-- Epimorphic alternating-face quasi-isomorphisms of simplicial abelian groups form a
subproperty of the underlying trivial Kan fibrations. -/
@[stacks 08P1 "alternating-face criterion for underlying trivial Kan fibrations"]
theorem alternatingFace :
    (MorphismProperty.epimorphisms (SimplicialObject AddCommGrpCat.{u}) ⊓
      (HomologicalComplex.quasiIso AddCommGrpCat.{u} (ComplexShape.down ℕ)).inverseImage
        (alternatingFaceMapComplex AddCommGrpCat.{u})) ≤
      Underlying.trivialKanFibrations (forget AddCommGrpCat) := by
  intro X Y f hf
  exact normalizedMoore f
    ⟨hf.1, (normalizedMoore_quasiIso_iff_alternatingFace f).2 hf.2⟩

namespace normalizedMoore

/-- An epimorphic normalized-Moore quasi-isomorphism of simplicial abelian groups is a trivial Kan
fibration on underlying simplicial sets. -/
@[stacks 08P1 "trivial Kan fibration criterion for simplicial abelian groups"]
theorem of_epi {f : X ⟶ Y} [Epi f]
    [QuasiIso ((normalizedMooreComplex AddCommGrpCat.{u}).map f)] :
    I.rlp (Functor.whiskerRight f (forget AddCommGrpCat)) := by
  exact normalizedMoore f
    ⟨inferInstance, inferInstanceAs (QuasiIso ((normalizedMooreComplex AddCommGrpCat).map f))⟩

/-- The degreewise-surjective normalized-Moore criterion with explicit assumptions. -/
@[stacks 08P1 "surjective normalized-Moore criterion with explicit assumptions"]
theorem of_surjective {f : X ⟶ Y}
    (hsurjective : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n))
    (hquasi : QuasiIso ((normalizedMooreComplex AddCommGrpCat.{u}).map f)) :
    I.rlp (Functor.whiskerRight f (forget AddCommGrpCat)) := by
  haveI : ∀ n : SimplexCategoryᵒᵖ, Epi (f.app n) :=
    fun n => (AddCommGrpCat.epi_iff_surjective (f.app n)).2 (hsurjective n)
  haveI : Epi f := NatTrans.epi_of_epi_app f
  haveI := hquasi
  exact of_epi

end normalizedMoore

namespace alternatingFace

/-- An epimorphic alternating-face quasi-isomorphism of simplicial abelian groups is a trivial
Kan fibration on underlying simplicial sets. -/
@[stacks 08P1 "categorical alternating-face trivial Kan fibration criterion"]
theorem of_epi {f : X ⟶ Y} [Epi f]
    [QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f)] :
    I.rlp (Functor.whiskerRight f (forget AddCommGrpCat)) := by
  exact alternatingFace f
    ⟨inferInstance, inferInstanceAs (QuasiIso ((alternatingFaceMapComplex AddCommGrpCat).map f))⟩

/-- The degreewise-surjective alternating-face criterion with explicit assumptions. -/
@[stacks 08P1 "surjective alternating-face criterion with explicit assumptions"]
theorem of_surjective {f : X ⟶ Y}
    (hsurjective : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n))
    (hquasi : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f)) :
    I.rlp (Functor.whiskerRight f (forget AddCommGrpCat)) := by
  haveI : ∀ n : SimplexCategoryᵒᵖ, Epi (f.app n) :=
    fun n => (AddCommGrpCat.epi_iff_surjective (f.app n)).2 (hsurjective n)
  haveI : Epi f := NatTrans.epi_of_epi_app f
  haveI := hquasi
  exact of_epi

end alternatingFace

end trivialKanFibrations

end underlying

end AddCommGrp

end CategoryTheory.SimplicialObject

open CategoryTheory

namespace AlgebraicTopology.normalizedMooreComplex

/-- The normalized-Moore and alternating-face functors pull back the chain-complex
quasi-isomorphism property to the same morphism property of simplicial objects. -/
@[stacks 08P1 "normalized and alternating quasi-isomorphism properties"]
theorem quasiIso_eq_alternatingFace {A : Type u} [Category.{v} A] [Abelian A] :
    (HomologicalComplex.quasiIso A (ComplexShape.down ℕ)).inverseImage
        (normalizedMooreComplex A) =
      (HomologicalComplex.quasiIso A (ComplexShape.down ℕ)).inverseImage
        (alternatingFaceMapComplex A) := by
  apply MorphismProperty.ext
  intro X Y f
  exact SimplicialObject.normalizedMoore_quasiIso_iff_alternatingFace f

/-- A simplicial morphism induces a quasi-isomorphism on its normalized Moore complex exactly when
it does so on its alternating-face complex. -/
@[stacks 08P1 "normalized and alternating Dold-Kan quasi-isomorphisms"]
theorem map.quasiIso_iff_alternatingFace {A : Type u} [Category.{v} A] [Abelian A]
    {X Y : SimplicialObject A} (f : X ⟶ Y) :
    QuasiIso ((normalizedMooreComplex A).map f) ↔
      QuasiIso ((alternatingFaceMapComplex A).map f) := by
  exact SimplicialObject.normalizedMoore_quasiIso_iff_alternatingFace f

/-- The normalized Moore complex of the kernel of an epimorphic quasi-isomorphism is acyclic. -/
@[stacks 08P1 "acyclic normalized Moore complex of a simplicial kernel"]
theorem kernel.acyclic_of_epi {A : Type u} [Category.{v} A] [Abelian A]
    {X Y : SimplicialObject A} {f : X ⟶ Y} [Epi f]
    [QuasiIso ((normalizedMooreComplex A).map f)] :
    ((normalizedMooreComplex A).obj (kernel f)).Acyclic := by
  haveI : (normalizedMooreComplex A).IsEquivalence :=
    Abelian.DoldKan.N.isEquivalence
  have hS : (ShortComplex.kernelSequence f).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact f
      epi_g := ‹Epi f› }
  exact (hS.map_of_exact (normalizedMooreComplex A)).acyclic_X₁
    (inferInstanceAs (QuasiIso ((normalizedMooreComplex A).map f)))

/-- Explicit-proof bridge for acyclicity of the normalized Moore kernel of an epimorphism. -/
@[stacks 08P1 "acyclic normalized Moore kernel with explicit assumptions"]
theorem kernel.acyclic_of_epi.explicit {A : Type u} [Category.{v} A] [Abelian A]
    {X Y : SimplicialObject A} {f : X ⟶ Y}
    (hepi : Epi f) (hquasi : QuasiIso ((normalizedMooreComplex A).map f)) :
    ((normalizedMooreComplex A).obj (kernel f)).Acyclic := by
  haveI := hepi
  haveI := hquasi
  exact acyclic_of_epi

end AlgebraicTopology.normalizedMooreComplex
