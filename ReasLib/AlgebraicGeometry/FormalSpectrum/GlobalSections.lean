/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.StructureSheaf
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.Algebra.Ring.Ideal

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite Topology TopologicalSpace
open AlgebraicGeometry.Spec (structureSheaf)

namespace AlgebraicGeometry.FormalSpectrum

section

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The algebra map from a quotient ring to the corresponding global component sections. -/
def quotientToComponent (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    A ⧸ I →+* componentType (⊤ : Opens (OpenPrime A)) I hI :=
  algebraMap (A ⧸ I)
    ((structureSheaf (A ⧸ I)).1.obj (op (pullbackOpens (⊤ : Opens (OpenPrime A)) I hI)))

/-- The quotient comparison is the canonical algebra map of structure-sheaf sections. -/
theorem quotientToComponent_apply (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (x : A ⧸ I) :
    quotientToComponent A I hI x =
      algebraMap (A ⧸ I)
        ((structureSheaf (A ⧸ I)).1.obj
          (op (pullbackOpens (⊤ : Opens (OpenPrime A)) I hI))) x := rfl

/-- The inverse affine global-sections comparison on a quotient component. -/
def componentToQuotient (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    componentType (⊤ : Opens (OpenPrime A)) I hI →+* A ⧸ I :=
  (StructureSheaf.globalSectionsIso (A ⧸ I)).inv.hom

/-- The quotient-component inverse recovers an element of the quotient ring. -/
theorem quotientToComponent_componentToQuotient (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) (x : A ⧸ I) :
    componentToQuotient A I hI (quotientToComponent A I hI x) = x := by
  change (StructureSheaf.globalSectionsIso (A ⧸ I)).inv.hom
      ((StructureSheaf.globalSectionsIso (A ⧸ I)).hom x) = x
  exact (StructureSheaf.globalSectionsIso (A ⧸ I)).hom_inv_id_apply x

/-- The component-to-quotient map is the inverse of the affine global-sections isomorphism. -/
theorem componentToQuotient_apply (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (s : componentType (⊤ : Opens (OpenPrime A)) I hI) :
    componentToQuotient A I hI s = (StructureSheaf.globalSectionsIso (A ⧸ I)).inv.hom s := rfl

private theorem componentToQuotient_quotientToComponent (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (s : componentType (⊤ : Opens (OpenPrime A)) I hI) :
    quotientToComponent A I hI (componentToQuotient A I hI s) = s := by
  change (StructureSheaf.globalSectionsIso (A ⧸ I)).hom.hom
      ((StructureSheaf.globalSectionsIso (A ⧸ I)).inv.hom s) = s
  exact (StructureSheaf.globalSectionsIso (A ⧸ I)).inv_hom_id_apply s

private theorem transition_quotientToComponent {I J : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ J) (x : A ⧸ I) :
    transition (⊤ : Opens (OpenPrime A)) hI hJ hIJ (quotientToComponent A I hI x) =
      quotientToComponent A J hJ (Ideal.Quotient.factor hIJ x) := by
  change StructureSheaf.comap (Ideal.Quotient.factor hIJ)
      (⊤ : Opens (PrimeSpectrum.Top (A ⧸ I)))
      (⊤ : Opens (PrimeSpectrum.Top (A ⧸ J))) _
      (algebraMap (A ⧸ I) ((structureSheaf (A ⧸ I)).1.obj (op ⊤)) x) =
    algebraMap (A ⧸ J) ((structureSheaf (A ⧸ J)).1.obj (op ⊤))
      ((Ideal.Quotient.factor hIJ) x)
  exact StructureSheaf.toOpen_comp_comap_apply (Ideal.Quotient.factor hIJ) ⊤ x

/-- The family of quotient sections determined by an element of the original ring. -/
def globalSectionFamily (a : A) : ComponentFamily (⊤ : Opens (OpenPrime A)) :=
  fun I ↦ quotientToComponent A I.val I.property (Ideal.Quotient.mk I.val a)

/-- The quotient section family is compatible and preserves the ring operations. -/
theorem globalSectionsHom_laws :
    (∀ a : A, IsCompatible ⊤ (globalSectionFamily a)) ∧
      globalSectionFamily (1 : A) = 1 ∧
      (∀ a b : A, globalSectionFamily (a * b) = globalSectionFamily a * globalSectionFamily b) ∧
      globalSectionFamily (0 : A) = 0 ∧
      (∀ a b : A, globalSectionFamily (a + b) = globalSectionFamily a + globalSectionFamily b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a I J hI hJ hIJ
    change transition (⊤ : Opens (OpenPrime A)) hI hJ hIJ
        (algebraMap (A ⧸ I)
          ((structureSheaf (A ⧸ I)).1.obj
            (op (pullbackOpens (⊤ : Opens (OpenPrime A)) I hI)))
          (Ideal.Quotient.mk I a)) =
      algebraMap (A ⧸ J)
        ((structureSheaf (A ⧸ J)).1.obj
          (op (pullbackOpens (⊤ : Opens (OpenPrime A)) J hJ)))
        (Ideal.Quotient.mk J a)
    change StructureSheaf.comap (Ideal.Quotient.factor hIJ)
        (⊤ : Opens (PrimeSpectrum.Top (A ⧸ I)))
        (⊤ : Opens (PrimeSpectrum.Top (A ⧸ J))) _
        (algebraMap (A ⧸ I) ((structureSheaf (A ⧸ I)).1.obj (op ⊤))
          (Ideal.Quotient.mk I a)) =
      algebraMap (A ⧸ J) ((structureSheaf (A ⧸ J)).1.obj (op ⊤))
        ((Ideal.Quotient.factor hIJ) (Ideal.Quotient.mk I a))
    exact StructureSheaf.toOpen_comp_comap_apply (Ideal.Quotient.factor hIJ) ⊤
      (Ideal.Quotient.mk I a)
  · ext I
    simp [globalSectionFamily]
  · intro a b
    funext I
    simp [globalSectionFamily]
  · ext I
    simp [globalSectionFamily]
  · intro a b
    funext I
    simp [globalSectionFamily]

/-- The canonical comparison from the original ring to global sections of its formal spectrum. -/
def globalSectionsHom (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    A →+* Sections (⊤ : Opens (OpenPrime A)) where
  toFun a := ofCompatible ⊤ (globalSectionFamily a) (globalSectionsHom_laws.1 a)
  map_one' := Subtype.ext globalSectionsHom_laws.2.1
  map_mul' a b := Subtype.ext (globalSectionsHom_laws.2.2.1 a b)
  map_zero' := Subtype.ext globalSectionsHom_laws.2.2.2.1
  map_add' a b := Subtype.ext (globalSectionsHom_laws.2.2.2.2 a b)

/-- The quotient elements determined by the components of a global section. -/
def sectionsToQuotients (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (s : Sections (⊤ : Opens (OpenPrime A))) :
    ∀ (I : Ideal A), TopologicalRing.Ideal.IsIdealOfDefinition I → A ⧸ I :=
  fun I hI ↦ componentToQuotient A I hI (s.component I hI)

/-- Each quotient projection is the affine inverse comparison of the section component. -/
theorem sectionsToQuotients_apply (s : Sections (⊤ : Opens (OpenPrime A)))
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    sectionsToQuotients A s I hI = componentToQuotient A I hI (s.component I hI) := rfl

private theorem sectionsToQuotients_factor (s : Sections (⊤ : Opens (OpenPrime A)))
    {I J : Ideal A} (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) (hIJ : I ≤ J) :
    Ideal.Quotient.factor hIJ (sectionsToQuotients A s I hI) =
      sectionsToQuotients A s J hJ := by
  have hinj : Function.Injective (quotientToComponent A J hJ) :=
    (show Function.LeftInverse (componentToQuotient A J hJ) (quotientToComponent A J hJ) from
      quotientToComponent_componentToQuotient J hJ).injective
  apply hinj
  rw [← transition_quotientToComponent hI hJ hIJ]
  change transition (⊤ : Opens (OpenPrime A)) hI hJ hIJ
      (quotientToComponent A I hI (componentToQuotient A I hI (s.component I hI))) =
    quotientToComponent A J hJ (componentToQuotient A J hJ (s.component J hJ))
  rw [componentToQuotient_quotientToComponent, componentToQuotient_quotientToComponent]
  exact s.property hI hJ hIJ

/-- The filter on `A` generated by the lifts of all quotient components of a global section:
for each ideal of definition `I`, the coset of elements reducing to the `I`-component. -/
def sectionFilter (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (s : Sections (⊤ : Opens (OpenPrime A))) : Filter A :=
  ⨅ I : {I : Ideal A // TopologicalRing.Ideal.IsIdealOfDefinition I},
    Filter.principal {a | Ideal.Quotient.mk I.val a = sectionsToQuotients A s I.val I.property}

/-- The global-sections comparison is continuous for the inverse-limit topology. -/
theorem globalSectionsHom_continuous : Continuous (globalSectionsHom A) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro I
  letI : DiscreteTopology (A ⧸ I.val) := QuotientAddGroup.discreteTopology I.property.1
  have hmk : Continuous (Ideal.Quotient.mk I.val) := continuous_quot_mk
  exact continuous_of_discreteTopology.comp hmk

end

variable {A : Type u} [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdmissibleRing A]

private theorem idealOfDefinition_nhds_basis :
    (𝓝 (0 : A)).HasBasis
      (fun _ : {I : Ideal A // TopologicalRing.Ideal.IsIdealOfDefinition I} => True)
      (fun I => (I.val : Set A)) := by
  obtain ⟨I, hI⟩ := TopologicalRing.IsPreadmissibleRing.exists_ideal_isIdealOfDefinition (R := A)
  refine (IsLinearTopology.hasBasis_open_ideal (R := A)).to_hasBasis ?_ ?_
  · intro J hJ
    have hIJ : TopologicalRing.Ideal.IsIdealOfDefinition (I ⊓ J) := by
      refine ⟨hI.1.inter hJ, ?_⟩
      intro U hU
      obtain ⟨n, hn⟩ := hI.2 U hU
      have hpow : (I ⊓ J) ^ n ≤ I ^ n := pow_le_pow_left' inf_le_left n
      exact ⟨n, fun x hx => hn (hpow hx)⟩
    exact ⟨⟨I ⊓ J, hIJ⟩, trivial, inf_le_right⟩
  · intro J _
    exact ⟨J.val, J.property.1, Set.Subset.rfl⟩

private theorem sectionFilter_basis (s : Sections (⊤ : Opens (OpenPrime A))) :
    (sectionFilter A s).HasBasis
      (fun _ : {I : Ideal A // TopologicalRing.Ideal.IsIdealOfDefinition I} => True)
      (fun I => {a | Ideal.Quotient.mk I.val a = sectionsToQuotients A s I.val I.property}) := by
  obtain ⟨I₀, hI₀⟩ :=
    TopologicalRing.IsPreadmissibleRing.exists_ideal_isIdealOfDefinition (R := A)
  letI : Nonempty {I : Ideal A // TopologicalRing.Ideal.IsIdealOfDefinition I} :=
    ⟨⟨I₀, hI₀⟩⟩
  apply Filter.hasBasis_iInf_principal
  intro I J
  have hK : TopologicalRing.Ideal.IsIdealOfDefinition (I.val ⊓ J.val) := by
    refine ⟨I.property.1.inter J.property.1, ?_⟩
    intro U hU
    obtain ⟨n, hn⟩ := I.property.2 U hU
    have hpow : (I.val ⊓ J.val) ^ n ≤ I.val ^ n := pow_le_pow_left' inf_le_left n
    exact ⟨n, fun x hx => hn (hpow hx)⟩
  refine ⟨⟨I.val ⊓ J.val, hK⟩, ?_, ?_⟩
  · intro a ha
    calc
      Ideal.Quotient.mk I.val a =
          Ideal.Quotient.factor inf_le_left (Ideal.Quotient.mk (I.val ⊓ J.val) a) := rfl
      _ = Ideal.Quotient.factor inf_le_left
          (sectionsToQuotients A s (I.val ⊓ J.val) hK) := congrArg _ ha
      _ = sectionsToQuotients A s I.val I.property :=
        sectionsToQuotients_factor s hK I.property inf_le_left
  · intro a ha
    calc
      Ideal.Quotient.mk J.val a =
          Ideal.Quotient.factor inf_le_right (Ideal.Quotient.mk (I.val ⊓ J.val) a) := rfl
      _ = Ideal.Quotient.factor inf_le_right
          (sectionsToQuotients A s (I.val ⊓ J.val) hK) := congrArg _ ha
      _ = sectionsToQuotients A s J.val J.property :=
        sectionsToQuotients_factor s hK J.property inf_le_right

private theorem sectionFilter_neBot (s : Sections (⊤ : Opens (OpenPrime A))) :
    Filter.NeBot (sectionFilter A s) := by
  apply (sectionFilter_basis s).neBot_iff.mpr
  intro I _
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (sectionsToQuotients A s I.val I.property)
  exact ⟨a, ha⟩

private theorem sectionFilter_cauchy_core (s : Sections (⊤ : Opens (OpenPrime A))) :
    @Cauchy A (IsTopologicalAddGroup.rightUniformSpace A) (sectionFilter A s) := by
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have hb := (idealOfDefinition_nhds_basis (A := A)).comap
    (fun p : A × A => p.2 - p.1)
  rw [← uniformity_eq_comap_nhds_zero A] at hb
  apply hb.cauchy_iff.mpr
  refine ⟨sectionFilter_neBot s, ?_⟩
  intro I _
  refine ⟨{a | Ideal.Quotient.mk I.val a = sectionsToQuotients A s I.val I.property},
    Filter.mem_iInf_of_mem I (by simp), ?_⟩
  intro x hx y hy
  exact Ideal.Quotient.eq.mp (hy.trans hx.symm)


private theorem sectionFilter_le_nhds_of_realizer (s : Sections (⊤ : Opens (OpenPrime A))) (a : A)
    (h : ∀ (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I),
      Ideal.Quotient.mk I a = sectionsToQuotients A s I hI) :
    sectionFilter A s ≤ 𝓝 a := by
  have hb := (idealOfDefinition_nhds_basis (A := A)).map (fun x : A => a + x)
  rw [map_add_left_nhds_zero] at hb
  apply hb.ge_iff.mpr
  intro I _
  have hmem : {b : A | Ideal.Quotient.mk I.val b = sectionsToQuotients A s I.val I.property} ∈
      sectionFilter A s := Filter.mem_iInf_of_mem I (by simp)
  refine Filter.mem_of_superset hmem ?_
  intro b hb
  refine ⟨b - a, ?_, by simp⟩
  apply Ideal.Quotient.eq.mp
  exact hb.trans (h I.val I.property).symm

private theorem sectionFilter_mk_of_le_nhds
    (s : Sections (⊤ : Opens (OpenPrime A))) (a : A) (ha : sectionFilter A s ≤ 𝓝 a)
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    Ideal.Quotient.mk I a = sectionsToQuotients A s I hI := by
  letI : Filter.NeBot (sectionFilter A s) := sectionFilter_neBot s
  letI : DiscreteTopology (A ⧸ I) := QuotientAddGroup.discreteTopology hI.1
  have hmk : Continuous (Ideal.Quotient.mk I) := continuous_quot_mk
  have hclosed : IsClosed {a : A | Ideal.Quotient.mk I a = sectionsToQuotients A s I hI} :=
    isClosed_singleton.preimage hmk
  have hmem : {a : A | Ideal.Quotient.mk I a = sectionsToQuotients A s I hI} ∈
      sectionFilter A s :=
    Filter.mem_iInf_of_mem ⟨I, hI⟩ (by simp)
  exact @IsClosed.mem_of_tendsto A _ A a
    {a : A | Ideal.Quotient.mk I a = sectionsToQuotients A s I hI}
    id (sectionFilter A s) (sectionFilter_neBot s) hclosed ha hmem

/-- An admissible ring has a unique element realizing the quotient components of a section. -/
theorem globalSectionsInv_existsUnique
    (s : Sections (⊤ : Opens (OpenPrime A))) :
    ∃! a : A, ∀ (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I),
      Ideal.Quotient.mk I a = sectionsToQuotients A s I hI := by
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  letI : CompleteSpace A := TopologicalRing.IsAdmissibleRing.isComplete
  letI : T2Space A := TopologicalRing.IsAdmissibleRing.isT2
  letI : Filter.NeBot (sectionFilter A s) := sectionFilter_neBot s
  obtain ⟨a, ha⟩ := CompleteSpace.complete (sectionFilter_cauchy_core s)
  refine ⟨a, sectionFilter_mk_of_le_nhds s a ha, ?_⟩
  intro b hb
  exact @tendsto_nhds_unique A A _ _ id (sectionFilter A s) b a
    (sectionFilter_neBot s) (sectionFilter_le_nhds_of_realizer s b hb) ha

/-- The element of an admissible ring determined by a global section: the limit, in the
complete separated topology of `A`, of the filter of lifts of all its quotient components. -/
def sectionLimit (s : Sections (⊤ : Opens (OpenPrime A))) : A :=
  Filter.lim (sectionFilter A s)

/-- Compatible quotient components give a Cauchy filter for the additive uniformity. -/
theorem sectionFilter_cauchy (s : Sections (⊤ : Opens (OpenPrime A))) :
    @Cauchy A (IsTopologicalAddGroup.rightUniformSpace A) (sectionFilter A s) :=
  sectionFilter_cauchy_core s

/-- The filter of quotient-component lifts of a global section converges to its limit element. -/
theorem sectionFilter_le_nhds_sectionLimit (s : Sections (⊤ : Opens (OpenPrime A))) :
    sectionFilter A s ≤ 𝓝 (sectionLimit s) :=
  @Cauchy.le_nhds_lim A (IsTopologicalAddGroup.rightUniformSpace A)
    inferInstance (sectionFilter A s) (sectionFilter_cauchy s)

private theorem sectionLimit_mk (s : Sections (⊤ : Opens (OpenPrime A))) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    Ideal.Quotient.mk I (sectionLimit s) = sectionsToQuotients A s I hI :=
  sectionFilter_mk_of_le_nhds s (sectionLimit s) (sectionFilter_le_nhds_sectionLimit s) I hI

private theorem sectionLimit_unique (s : Sections (⊤ : Opens (OpenPrime A))) (a : A)
    (h : ∀ (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I),
      Ideal.Quotient.mk I a = sectionsToQuotients A s I hI) :
    a = sectionLimit s :=
  (globalSectionsInv_existsUnique s).unique h (sectionLimit_mk s)

/-- Reconstruction from quotient components preserves the ring operations. -/
theorem globalSectionsInvHom_laws :
    sectionLimit (1 : Sections (⊤ : Opens (OpenPrime A))) = 1 ∧
      (∀ s t : Sections (⊤ : Opens (OpenPrime A)),
        sectionLimit (s * t) = sectionLimit s * sectionLimit t) ∧
      sectionLimit (0 : Sections (⊤ : Opens (OpenPrime A))) = 0 ∧
      (∀ s t : Sections (⊤ : Opens (OpenPrime A)),
        sectionLimit (s + t) = sectionLimit s + sectionLimit t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Eq.symm
    apply sectionLimit_unique
    intro I hI
    change Ideal.Quotient.mk I 1 = componentToQuotient A I hI 1
    simp
  · intro s t
    apply Eq.symm
    apply sectionLimit_unique
    intro I hI
    change Ideal.Quotient.mk I (sectionLimit s * sectionLimit t) =
      componentToQuotient A I hI (s.component I hI * t.component I hI)
    rw [map_mul, sectionLimit_mk s, sectionLimit_mk t]
    exact (map_mul (componentToQuotient A I hI) _ _).symm
  · apply Eq.symm
    apply sectionLimit_unique
    intro I hI
    change Ideal.Quotient.mk I 0 = componentToQuotient A I hI 0
    simp
  · intro s t
    apply Eq.symm
    apply sectionLimit_unique
    intro I hI
    change Ideal.Quotient.mk I (sectionLimit s + sectionLimit t) =
      componentToQuotient A I hI (s.component I hI + t.component I hI)
    rw [map_add, sectionLimit_mk s, sectionLimit_mk t]
    exact (map_add (componentToQuotient A I hI) _ _).symm

/-- The ring homomorphism reconstructing an admissible-ring element from its global section. -/
def globalSectionsInvHom (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdmissibleRing A] : Sections (⊤ : Opens (OpenPrime A)) →+* A where
  toFun := sectionLimit
  map_one' := globalSectionsInvHom_laws.1
  map_mul' := globalSectionsInvHom_laws.2.1
  map_zero' := globalSectionsInvHom_laws.2.2.1
  map_add' := globalSectionsInvHom_laws.2.2.2

/-- The reconstruction homomorphism evaluates a section to its limit element. -/
theorem globalSectionsInvHom_apply (s : Sections (⊤ : Opens (OpenPrime A))) :
    globalSectionsInvHom A s = sectionLimit s := rfl

/-- Reconstruction recovers every quotient component of a global section. -/
theorem globalSectionsInvHom_mk
    (s : Sections (⊤ : Opens (OpenPrime A))) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    Ideal.Quotient.mk I (globalSectionsInvHom A s) = sectionsToQuotients A s I hI :=
  sectionLimit_mk s I hI

/-- Reconstruction is independent of the realizing element, which is uniquely determined. -/
theorem globalSectionsInvHom_unique
    (s : Sections (⊤ : Opens (OpenPrime A))) (a : A)
    (h : ∀ (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I),
      Ideal.Quotient.mk I a = sectionsToQuotients A s I hI) :
    a = globalSectionsInvHom A s :=
  sectionLimit_unique s a h

/-- The global-sections comparison of an admissible ring is bijective. -/
theorem globalSectionsHom_bijective :
    Function.Bijective (globalSectionsHom A) := by
  have hleft : Function.LeftInverse (globalSectionsInvHom A) (globalSectionsHom A) := by
    intro a
    apply Eq.symm
    apply globalSectionsInvHom_unique
    intro I hI
    exact (quotientToComponent_componentToQuotient I hI (Ideal.Quotient.mk I a)).symm
  have hright : Function.RightInverse (globalSectionsInvHom A) (globalSectionsHom A) := by
    intro s
    apply Subtype.ext
    funext I
    change quotientToComponent A I.val I.property
        (Ideal.Quotient.mk I.val (globalSectionsInvHom A s)) = s.component I.val I.property
    rw [globalSectionsInvHom_mk]
    change (StructureSheaf.globalSectionsIso (A ⧸ I.val)).hom.hom
        ((StructureSheaf.globalSectionsIso (A ⧸ I.val)).inv.hom
          (s.component I.val I.property)) = s.component I.val I.property
    exact (StructureSheaf.globalSectionsIso (A ⧸ I.val)).inv_hom_id_apply _
  exact ⟨hleft.injective, hright.surjective⟩

/-- Reconstruction is continuous for the topology of an admissible ring. -/
theorem globalSectionsInvHom_continuous :
    Continuous (globalSectionsInvHom A) := by
  apply continuous_of_tendsto_nhds_zero (globalSectionsInvHom A)
  apply (idealOfDefinition_nhds_basis (A := A)).tendsto_right_iff.mpr
  intro I _
  letI : DiscreteTopology (A ⧸ I.val) := QuotientAddGroup.discreteTopology I.property.1
  letI : DiscreteTopology (componentType (⊤ : Opens (OpenPrime A)) I.val I.property) :=
    isDiscrete_componentType_of_isCompact ⊤ I.val I.property (by
      change IsCompact (Set.univ : Set (PrimeSpectrum (A ⧸ I.val)))
      exact isCompact_univ)
  have hc : Continuous (fun s : Sections (⊤ : Opens (OpenPrime A)) =>
      s.component I.val I.property) :=
    (continuous_apply I).comp continuous_subtype_val
  have hq : Continuous (fun s : Sections (⊤ : Opens (OpenPrime A)) =>
      sectionsToQuotients A s I.val I.property) :=
    continuous_of_discreteTopology.comp hc
  have hmem : {s : Sections (⊤ : Opens (OpenPrime A)) |
      sectionsToQuotients A s I.val I.property = 0} ∈ 𝓝 0 := by
    apply (isOpen_discrete ({0} : Set (A ⧸ I.val))).preimage hq |>.mem_nhds
    change componentToQuotient A I.val I.property 0 = 0
    exact map_zero _
  refine Filter.mem_of_superset hmem ?_
  intro s hs
  exact Ideal.Quotient.eq_zero_iff_mem.mp ((globalSectionsInvHom_mk s I.val I.property).trans hs)

end AlgebraicGeometry.FormalSpectrum
