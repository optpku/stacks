/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.FunctorialApproximation

@[expose] public section

/-!
# Functorial approximations killing acyclic complexes

This module refines `FunctorialComplexApproximation` by recording that maps from a fixed family
of complexes become null-homotopic after the comparison map. The refinement itself makes sense
for an arbitrary family; acyclicity and the Grothendieck hypothesis occur only in its existence
theorem.
-/

open CategoryTheory Limits

universe w v u

namespace CochainComplex

variable {I : Type w}

section Neutral

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C]

/-- A functorial acyclic-killing approximation is a functorial complex approximation such that
every map from a member of `K` becomes null-homotopic after the comparison map. -/
@[stacks 079M "functorial acyclic-killing approximation"]
structure FunctorialAcyclicKilling (K : I → CochainComplex C ℤ) extends
    toApproximation : FunctorialComplexApproximation C where
  /-- Every map from the selected family becomes null-homotopic after entering the
  approximation. -/
  nullHomotopic (i : I) (M : CochainComplex C ℤ) (f : K i ⟶ M) :
    Nonempty (Homotopy (f ≫ toApproximation.ι.app M) 0)

end Neutral

namespace FunctorialAcyclicKilling

section Grothendieck

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The small set of pairs consisting of a test complex and an actual map to `M`. -/
abbrev TestMapIndex (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) : Type w :=
  Σ i : I, Shrink.{w} (K i ⟶ M)

/-- Recover the actual morphism represented by a small test-map index. -/
noncomputable def testMap (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ)
    (a : TestMapIndex K M) : K a.1 ⟶ M :=
  (equivShrink (K a.1 ⟶ M)).symm a.2

/-- The index associated with a specified test morphism. -/
noncomputable def testMapIndex (K : I → CochainComplex C ℤ) {M : CochainComplex C ℤ}
    (i : I) (f : K i ⟶ M) : TestMapIndex K M :=
  ⟨i, equivShrink (K i ⟶ M) f⟩

/-- Shrinking the index does not change its represented morphism. -/
@[simp]
theorem testMap_testMapIndex (K : I → CochainComplex C ℤ) {M : CochainComplex C ℤ}
    (i : I) (f : K i ⟶ M) : testMap K M (testMapIndex K i f) = f := by
  exact (equivShrink (K i ⟶ M)).symm_apply_apply f

/-- The coproduct of all test complexes with their chosen maps to `M`. -/
noncomputable abbrev testCoproduct (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :=
  ∐ (fun a : TestMapIndex K M ↦ K a.1)

/-- The corresponding coproduct of identity mapping cones. -/
noncomputable abbrev coneCoproduct (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :=
  ∐ (fun a : TestMapIndex K M ↦ mappingCone (𝟙 (K a.1)))

/-- The universal evaluation map from all indexed test morphisms. -/
noncomputable def evaluation (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :
    testCoproduct K M ⟶ M :=
  Sigma.desc (testMap K M)

/-- The coproduct of the actual inclusions into the identity mapping cones. -/
noncomputable def coneInclusion (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :
    testCoproduct K M ⟶ coneCoproduct K M :=
  Sigma.desc (fun a ↦ mappingCone.inr (𝟙 (K a.1)) ≫
    Sigma.ι (fun b : TestMapIndex K M ↦ mappingCone (𝟙 (K b.1))) a)

/-- The source construction attaches identity cones along all test morphisms. -/
noncomputable def approximationComplex (K : I → CochainComplex C ℤ)
    (M : CochainComplex C ℤ) : CochainComplex C ℤ :=
  pushout (evaluation K M) (coneInclusion K M)

/-- The comparison is the first coprojection of the actual pushout. -/
noncomputable def comparison (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :
    M ⟶ approximationComplex K M :=
  pushout.inl (evaluation K M) (coneInclusion K M)

/-- Each attached cone maps to the pushout through its specified coproduct inclusion. -/
noncomputable def attachedConeMap (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ)
    (a : TestMapIndex K M) : mappingCone (𝟙 (K a.1)) ⟶ approximationComplex K M :=
  Sigma.ι (fun b : TestMapIndex K M ↦ mappingCone (𝟙 (K b.1))) a ≫
    pushout.inr (evaluation K M) (coneInclusion K M)

set_option backward.isDefEq.respectTransparency false in
/-- The attaching equation identifies the image of each test morphism. -/
@[reassoc (attr := simp)]
theorem testMap_comparison (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ)
    (a : TestMapIndex K M) :
    testMap K M a ≫ comparison K M =
      mappingCone.inr (𝟙 (K a.1)) ≫ attachedConeMap K M a := by
  have h := congrArg (fun f ↦ Sigma.ι (fun b : TestMapIndex K M ↦ K b.1) a ≫ f)
    (pushout.condition (f := evaluation K M) (g := coneInclusion K M))
  simpa [evaluation, coneInclusion, comparison, attachedConeMap, Category.assoc] using h

/-- Reindex attached cones by composing the represented test morphism with `f`. -/
noncomputable def approximationMap (K : I → CochainComplex C ℤ)
    {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    approximationComplex K M ⟶ approximationComplex K N :=
  pushout.desc (f ≫ comparison K N)
    (Sigma.desc (fun a : TestMapIndex K M ↦
      attachedConeMap K N (testMapIndex K a.1 (testMap K M a ≫ f)))) (by sorry)

set_option backward.isDefEq.respectTransparency false in
/-- The action on morphisms agrees with the given map on the original complex. -/
@[reassoc (attr := simp)]
theorem comparison_approximationMap (K : I → CochainComplex C ℤ)
    {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    comparison K M ≫ approximationMap K f = f ≫ comparison K N := by
  dsimp only [comparison, approximationMap]
  simp only [pushout.inl_desc]

set_option backward.isDefEq.respectTransparency false in
/-- An attached cone is carried to the cone indexed by the composed test morphism. -/
@[reassoc (attr := simp)]
theorem attachedConeMap_approximationMap (K : I → CochainComplex C ℤ)
    {M N : CochainComplex C ℤ} (f : M ⟶ N) (a : TestMapIndex K M) :
    attachedConeMap K M a ≫ approximationMap K f =
      attachedConeMap K N (testMapIndex K a.1 (testMap K M a ≫ f)) := by
  dsimp only [attachedConeMap, approximationMap]
  simp only [Category.assoc, pushout.inr_desc, Sigma.ι_desc]

/-- The pushout construction with all test morphisms is functorial. -/
noncomputable def approximationFunctor (K : I → CochainComplex C ℤ) :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj := approximationComplex K
  map := approximationMap K
  map_id := sorry
  map_comp := sorry

/-- The pushout coprojections give the source's natural comparison. -/
noncomputable def approximationComparison (K : I → CochainComplex C ℤ) :
    𝟭 (CochainComplex C ℤ) ⟶ approximationFunctor K where
  app := comparison K
  naturality := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion into the identity mapping cone has the native explicit nullhomotopy. -/
noncomputable def coneInclusionHomotopy (L : CochainComplex C ℤ) :
    Homotopy (mappingCone.inr (𝟙 L)) 0 := by
  simpa only [Category.id_comp, mappingCone.inr] using
    HomologicalComplex.homotopyCofiber.inrCompHomotopy (𝟙 L)
      (fun j ↦ ⟨j - 1, by change j - 1 + 1 = j; omega⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The native cone homotopy followed by the attached cone map kills each specified test map. -/
noncomputable def nullHomotopy (K : I → CochainComplex C ℤ) (i : I)
    (M : CochainComplex C ℤ) (f : K i ⟶ M) :
    Homotopy (f ≫ (approximationComparison K).app M) 0 :=
  (Homotopy.ofEq (by
    have h := testMap_comparison K M (testMapIndex K i f)
    rw [testMap_testMapIndex] at h
    exact h)).trans
    (((coneInclusionHomotopy (K i)).compRight
      (attachedConeMap K M (testMapIndex K i f))).trans
        (Homotopy.ofEq (by simp)))

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise homotopy map is the actual cone homotopy followed by its attaching map. -/
@[simp]
theorem nullHomotopy_hom (K : I → CochainComplex C ℤ) (i : I)
    (M : CochainComplex C ℤ) (f : K i ⟶ M) (p q : ℤ) :
    (nullHomotopy K i M f).hom p q =
      (coneInclusionHomotopy (K i)).hom p q ≫
        (attachedConeMap K M (testMapIndex K i f)).f q := by
  simp only [nullHomotopy, Homotopy.trans, Homotopy.ofEq, Homotopy.compRight,
    zero_add, add_zero]

/-- The comparison maps in the acyclic-family construction are monomorphisms. -/
theorem comparison_mono (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :
    Mono (comparison K M) := sorry

/-- Acyclicity of the attached family makes the comparison a quasi-isomorphism. -/
theorem comparison_quasiIso (K : I → CochainComplex C ℤ)
    (hK : ∀ i, (K i).Acyclic) (M : CochainComplex C ℤ) :
    QuasiIso (comparison K M) := sorry

/-- Package the actual pushout and cone homotopies for an acyclic family. -/
noncomputable def ofAcyclicFamily (K : I → CochainComplex C ℤ)
    (hK : ∀ i, (K i).Acyclic) : FunctorialAcyclicKilling K where
  toFunctor := approximationFunctor K
  ι := approximationComparison K
  mono_app := comparison_mono K
  quasiIso_app := comparison_quasiIso K hK
  nullHomotopic i M f := ⟨nullHomotopy K i M f⟩

/-- Lemma 19.12.4: a family of acyclic complexes in a Grothendieck abelian category admits a
functorial acyclic-killing approximation. -/
@[stacks 079M "bundled existence"]
theorem nonempty (K : I → CochainComplex C ℤ) (hK : ∀ i, (K i).Acyclic) :
    Nonempty (FunctorialAcyclicKilling K) := ⟨ofAcyclicFamily K hK⟩

/-- The unbundled existential view of a functorial acyclic-killing approximation. -/
@[stacks 079M "existential view"]
theorem exists_approximation (K : I → CochainComplex C ℤ) (hK : ∀ i, (K i).Acyclic) :
    ∃ J : FunctorialComplexApproximation C,
      ∀ (i : I) (M : CochainComplex C ℤ) (f : K i ⟶ M),
        Nonempty (Homotopy (f ≫ J.ι.app M) 0) :=
  ⟨(ofAcyclicFamily K hK).toApproximation, fun i M f ↦ ⟨nullHomotopy K i M f⟩⟩

end Grothendieck

end FunctorialAcyclicKilling

end CochainComplex
