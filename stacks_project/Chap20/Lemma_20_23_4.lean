/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Fin.Tuple.Sort
public import stacks_project.Chap20.Definition_20_23_1
public import stacks_project.Chap20.Definition_20_23_2
public import ReasLib.Topology.Presheaf.Cech.TermIso
public import ReasLib.Topology.Opens.Instances

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open CategoryTheory.Limits.CompleteLattice
open scoped BigOperators

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]

/- Domain-style sampling for Lemma 20.23.4:
- primary domain: comparison morphisms between the ordinary, ordered, and alternating Čech
  cochain complexes attached to a linearly ordered cover;
- sampled owner declarations:
  `alternatingCechComplex`,
  `alternatingCechInclusion`,
  `cechComplexFunctor`,
  `orderedCechComplexOfOrder`,
  `orderedCechComplex`;
- best owner abstraction: the ordinary Čech complex stays at the canonical owner
  `cechComplexFunctor 𝒰`, the ordered complex stays at the chapter owner `orderedCechComplex 𝒰 F`,
  and the alternating complex is already owned upstream by `alternatingCechComplex 𝒰 F`; this file
  should keep only the ordered/alternating bridge maps.

Source/core/bridge triage:
- `source-facing`: the comparison/projection morphisms of Lemma 20.23.4;
- `core/canonical`: `alternatingCechComplex 𝒰 F`, `alternatingCechInclusion 𝒰 F`,
  `cechComplexFunctor 𝒰`, and `orderedCechComplexOfOrder o 𝒰 F` from earlier in the chapter;
- `bridge/view`: `alternatingCechInclusion`, `cechProjectionToOrderedCech`, and the derived
  composite `alternatingCechProjection`.

Primitive data versus derived API:
- primitive data: the ordered tuple model and the sorting permutation used to compare it with the
  alternating owner;
- derived API: the projection to the ordered Čech complex, the ordered-to-alternating comparison
  morphism, and the resulting composite `alternatingCechProjection`. -/

/-- Sorting an injective tuple produces the corresponding strictly increasing Čech tuple. -/
def sortedStrictCechTupleOfInjective {p : ℕ} (σ : Fin (p + 1) → ι)
    (hσ : Function.Injective σ) : OrderedCechIndex ι p :=
  OrderEmbedding.ofStrictMono (σ ∘ Tuple.sort σ)
    ((Tuple.monotone_sort σ).strictMono_of_injective
      (hσ.comp (Tuple.sort σ).injective))

/-- Sorting after permuting an injective tuple gives the same strictly increasing tuple. -/
theorem sortedStrictCechTupleOfInjective_comp_perm {p : ℕ}
    (σ : Fin (p + 1) → ι) (hσ : Function.Injective σ) (τ : Equiv.Perm (Fin (p + 1))) :
    sortedStrictCechTupleOfInjective (σ ∘ τ) (hσ.comp τ.injective) =
      sortedStrictCechTupleOfInjective σ hσ := by
  have hsortEq : ((σ ∘ τ) ∘ Tuple.sort (σ ∘ τ)) = σ ∘ Tuple.sort σ :=
    Tuple.comp_perm_comp_sort_eq_comp_sort
  ext i
  change ((σ ∘ τ) ∘ Tuple.sort (σ ∘ τ)) i = (σ ∘ Tuple.sort σ) i
  simpa [Function.comp_assoc] using congrFun hsortEq i

/-- Sorting after permuting an injective tuple changes the sorting sign by the sign of the
permutation. -/
theorem sign_sort_comp_perm {p : ℕ}
    (σ : Fin (p + 1) → ι) (hσ : Function.Injective σ) (τ : Equiv.Perm (Fin (p + 1))) :
    Equiv.Perm.sign (Tuple.sort (σ ∘ τ)) =
      Equiv.Perm.sign τ * Equiv.Perm.sign (Tuple.sort σ) := by
  have hsortEq : ((σ ∘ τ) ∘ Tuple.sort (σ ∘ τ)) = σ ∘ Tuple.sort σ :=
    Tuple.comp_perm_comp_sort_eq_comp_sort
  have hsort : Tuple.sort (σ ∘ τ) = (Tuple.sort σ).trans τ.symm := by
    have htrans : (Tuple.sort (σ ∘ τ)).trans τ = Tuple.sort σ := by
      ext j
      have hj : ((Tuple.sort (σ ∘ τ)).trans τ) j = (Tuple.sort σ) j := by
        apply hσ
        simpa [Function.comp_assoc] using congrFun hsortEq j
      exact congrArg Fin.val hj
    ext i
    have hi : τ ((Tuple.sort (σ ∘ τ)) i) = τ (((Tuple.sort σ).trans τ.symm) i) := by
      change ((Tuple.sort (σ ∘ τ)).trans τ) i = ((Tuple.sort σ).trans τ.symm).trans τ i
      rw [htrans]
      simp
    have hi' : (Tuple.sort (σ ∘ τ)) i = ((Tuple.sort σ).trans τ.symm) i := τ.injective hi
    exact congrArg Fin.val hi'
  calc
    Equiv.Perm.sign (Tuple.sort (σ ∘ τ)) =
        Equiv.Perm.sign ((Tuple.sort σ).trans τ.symm) := by
          rw [hsort]
    _ = Equiv.Perm.sign τ.symm * Equiv.Perm.sign (Tuple.sort σ) := by
          rw [Equiv.Perm.sign_trans]
    _ = Equiv.Perm.sign τ * Equiv.Perm.sign (Tuple.sort σ) := by
          simpa using
            congrArg (fun z : ℤ ↦ z * Equiv.Perm.sign (Tuple.sort σ)) (Equiv.Perm.sign_inv τ)

/-- Sorting an injective tuple does not change the associated Čech intersection. -/
theorem cechIntersection_sortedStrictCechTupleOfInjective
    (𝒰 : ι → Opens X) {p : ℕ} (σ : Fin (p + 1) → ι) (hσ : Function.Injective σ) :
    cechIntersection 𝒰 (sortedStrictCechTupleOfInjective σ hσ) = cechIntersection 𝒰 σ := by
  simpa [sortedStrictCechTupleOfInjective] using
    cechIntersection_comp_perm 𝒰 σ (Tuple.sort σ)

theorem addCommGrpCat_eqToHom_apply_orderedCech {A B : AddCommGrpCat} (h : A = B) (x : A) :
    (AddCommGrpCat.Hom.hom (eqToHom h)) x =
      cast (congrArg (fun Z : AddCommGrpCat ↦ ↥Z) h) x := by
  cases h
  rfl

theorem cast_strictCechSection_eq (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) {p : ℕ}
    (f : (σ : StrictCechTuple p) → F.obj (op (cechIntersection 𝒰 σ)))
    {σ τ : StrictCechTuple p} (h : σ = τ) :
    cast
        (congrArg
          (fun Z : AddCommGrpCat.{max u v} ↦ ↥Z)
          (congrArg (fun ν : StrictCechTuple p ↦ F.obj (op (cechIntersection 𝒰 ν))) h))
        (f σ) =
      f τ := by
  cases h
  rfl

abbrev cechProjectionToOrderedCechComponent (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    ((cechComplexFunctor 𝒰).obj F).X p ⟶ (orderedCechComplex 𝒰 F).X p :=
  (TopCat.Presheaf.Cech.termIso 𝒰 F p).hom ≫
    AddCommGrpCat.ofHom
      (AddMonoidHom.mk'
        (fun s σ ↦ s σ)
        (fun _ _ ↦ rfl))

theorem cechProjectionToOrderedCechComponent_comm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    cechProjectionToOrderedCechComponent 𝒰 F p ≫ (orderedCechComplex 𝒰 F).d p (p + 1) =
      ((cechComplexFunctor 𝒰).obj F).d p (p + 1) ≫
        cechProjectionToOrderedCechComponent 𝒰 F (p + 1) := sorry

/-- The extension of an ordered Čech cochain to an alternating Čech cochain obtained by sorting an
injective tuple and inserting the corresponding sign, and by sending tuples with repetitions to
zero. -/
def orderedCechComparisonToFun (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (orderedCechComplex 𝒰 F).X p → cechTerm 𝒰 F p :=
  fun s σ ↦
    if hσ : Function.Injective σ then
      let τ := Tuple.sort σ
      let σ' : StrictCechTuple p := sortedStrictCechTupleOfInjective σ hσ
      (Equiv.Perm.sign τ) •
        F.map (eqToHom (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 σ hσ).symm).op (s σ')
    else
      0

/-- On a strictly increasing tuple, the ordered-to-alternating extension recovers the original
ordered cochain. -/
theorem orderedCechComparisonToFun_apply_strict (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (orderedCechComplex 𝒰 F).X p) (σ : StrictCechTuple p) :
    orderedCechComparisonToFun 𝒰 F p s σ = s σ := by
  have hσ : Function.Injective (σ : Fin (p + 1) → ι) := σ.injective
  have hsort :
      Tuple.sort (σ : Fin (p + 1) → ι) = Equiv.refl (Fin (p + 1)) :=
    (Tuple.sort_eq_refl_iff_monotone).2 σ.monotone
  have hsorted : sortedStrictCechTupleOfInjective (σ : Fin (p + 1) → ι) hσ = σ := by
    ext i
    simpa [sortedStrictCechTupleOfInjective, hsort]
  rw [orderedCechComparisonToFun, dif_pos hσ, hsort]
  have hterm :
      F.map
          (eqToHom
            (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 (σ : Fin (p + 1) → ι) hσ).symm).op
          (s (sortedStrictCechTupleOfInjective (σ : Fin (p + 1) → ι) hσ)) =
        s σ := by
    have hcech :
        cechIntersection_sortedStrictCechTupleOfInjective 𝒰 (σ : Fin (p + 1) → ι) hσ =
          congrArg (cechIntersection 𝒰) (congrArg DFunLike.coe hsorted) := by
      apply Subsingleton.elim
    rw [hcech]
    erw [eqToHom_op, eqToHom_map]
    simpa [addCommGrpCat_eqToHom_apply_orderedCech] using
      cast_strictCechSection_eq 𝒰 F s hsorted
  simpa using hterm

/-- Extending the restriction of an alternating cochain back from strictly increasing tuples
recovers the original alternating cochain. -/
theorem orderedCechComparisonToFun_eq_of_alternating (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : alternatingCechTerm 𝒰 F p) :
    orderedCechComparisonToFun 𝒰 F p (fun σ ↦ s.1 σ) = s.1 := sorry

-- Proof sketch: by construction the comparison map kills tuples with repeated indices and its
-- value on an injective tuple changes by the sign of the reordering permutation.
/-- The ordered-to-alternating comparison formula lands in alternating Čech cochains. -/
theorem orderedCechComparisonToFun_mem_alternating (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (s : (orderedCechComplex 𝒰 F).X p) :
    IsAlternatingCechCochain 𝒰 F p (orderedCechComparisonToFun 𝒰 F p s) := by
  constructor
  · intro σ hσ
    simp [orderedCechComparisonToFun, hσ]
  · intro σ τ
    by_cases hσ : Function.Injective σ
    · have hστ : Function.Injective (σ ∘ τ) := hσ.comp τ.injective
      let σ' : StrictCechTuple p := sortedStrictCechTupleOfInjective σ hσ
      let στ' : StrictCechTuple p :=
        sortedStrictCechTupleOfInjective (σ ∘ τ) hστ
      have hsorted : στ' = σ' := by
        simpa [σ', στ'] using sortedStrictCechTupleOfInjective_comp_perm σ hσ τ
      rw [orderedCechComparisonToFun, dif_pos hστ, orderedCechComparisonToFun, dif_pos hσ]
      dsimp
      have hmap_zsmul :
          (ConcreteCategory.hom (F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op))
              (Equiv.Perm.sign (Tuple.sort (σ ∘ τ)) •
                (ConcreteCategory.hom
                  (F.map
                    (eqToHom
                      (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 (σ ∘ τ) hστ).symm).op))
                  (s (sortedStrictCechTupleOfInjective (σ ∘ τ) hστ))) =
            Equiv.Perm.sign (Tuple.sort (σ ∘ τ)) •
              F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op
                (F.map
                  (eqToHom
                    (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 (σ ∘ τ) hστ).symm).op
                  (s (sortedStrictCechTupleOfInjective (σ ∘ τ) hστ))) := by
        simpa using
          map_zsmul
            (ConcreteCategory.hom (F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op))
            (Equiv.Perm.sign (Tuple.sort (σ ∘ τ)))
            ((ConcreteCategory.hom
              (F.map
                (eqToHom
                  (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 (σ ∘ τ) hστ).symm).op))
              (s (sortedStrictCechTupleOfInjective (σ ∘ τ) hστ)))
      rw [hmap_zsmul, sign_sort_comp_perm σ hσ τ]
      have hterm :
          F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op
              (F.map
                (eqToHom
                  (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 (σ ∘ τ) hστ).symm).op
                (s στ')) =
            F.map
              (eqToHom
                (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 σ hσ).symm).op
              (s σ') := by
        have hd :
            cechIntersection 𝒰 στ' = cechIntersection 𝒰 σ' := by
          exact congrArg (cechIntersection 𝒰) (congrArg DFunLike.coe hsorted)
        have hs :
            F.map (eqToHom hd.symm).op (s στ') = s σ' := by
          erw [eqToHom_op, eqToHom_map]
          simpa [addCommGrpCat_eqToHom_apply_orderedCech] using cast_strictCechSection_eq 𝒰 F s hsorted
        have hcomp :
            eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm ≫
                eqToHom
                  (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 (σ ∘ τ) hστ).symm =
              eqToHom
                  (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 σ hσ).symm ≫
                eqToHom hd.symm := by
          apply Subsingleton.elim
        calc
          F.map (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op
              (F.map
                (eqToHom
                  (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 (σ ∘ τ) hστ).symm).op
                (s στ')) =
            F.map
              ((eqToHom
                (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 (σ ∘ τ) hστ).symm).op ≫
                (eqToHom (cechIntersection_comp_perm 𝒰 σ τ).symm).op) (s στ') := by
                  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
          _ =
            F.map
              ((eqToHom hd.symm).op ≫
                (eqToHom
                  (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 σ hσ).symm).op) (s στ') := by
                  simpa using congrArg F.map (congrArg Quiver.Hom.op hcomp)
          _ =
            F.map
              (eqToHom
                (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 σ hσ).symm).op
              (F.map (eqToHom hd.symm).op (s στ')) := by
                rw [Functor.map_comp, ConcreteCategory.comp_apply]
          _ = F.map
              (eqToHom
                (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 σ hσ).symm).op
              (s σ') := by rw [hs]
      simpa [mul_smul] using
        congrArg ((Equiv.Perm.sign τ * Equiv.Perm.sign (Tuple.sort σ)) • ·) hterm
    · have hστ : ¬ Function.Injective (σ ∘ τ) := by
        intro h
        have hσ' : Function.Injective ((σ ∘ τ) ∘ τ.symm) := h.comp τ.symm.injective
        exact hσ (by simpa [Function.comp_assoc] using hσ')
      simp [orderedCechComparisonToFun, hσ, hστ]

-- Proof sketch: the extension formula for `c` is linear in the ordered cochain.
/-- The ordered-to-alternating comparison map is additive on cochains. -/
theorem orderedCechComparisonToFun_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : (orderedCechComplex 𝒰 F).X p) :
    orderedCechComparisonToFun 𝒰 F p (s + t) =
      orderedCechComparisonToFun 𝒰 F p s + orderedCechComparisonToFun 𝒰 F p t := sorry

-- Proof sketch: the packaged alternating cochain is defined from the linear extension formula for
-- `c`, so additivity is inherited from `orderedCechComparisonToFun`.
theorem orderedCechComparisonComponent_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : (orderedCechComplex 𝒰 F).X p) :
    (⟨orderedCechComparisonToFun 𝒰 F p (s + t),
        orderedCechComparisonToFun_mem_alternating 𝒰 F p (s + t)⟩ :
      alternatingCechTerm 𝒰 F p) =
      ⟨orderedCechComparisonToFun 𝒰 F p s,
        orderedCechComparisonToFun_mem_alternating 𝒰 F p s⟩ +
        ⟨orderedCechComparisonToFun 𝒰 F p t,
          orderedCechComparisonToFun_mem_alternating 𝒰 F p t⟩ := by
  apply Subtype.ext
  ext σ
  exact congrFun (orderedCechComparisonToFun_map_add 𝒰 F p s t) σ

abbrev orderedCechComparisonComponent (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (orderedCechComplex 𝒰 F).X p ⟶ (alternatingCechComplex 𝒰 F).X p :=
  AddCommGrpCat.ofHom
    (AddMonoidHom.mk'
      (fun s ↦
        ⟨orderedCechComparisonToFun 𝒰 F p s,
          orderedCechComparisonToFun_mem_alternating 𝒰 F p s⟩)
      (orderedCechComparisonComponent_map_add 𝒰 F p))

abbrev alternatingCechProjectionComponent (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (alternatingCechComplex 𝒰 F).X p ⟶ (orderedCechComplex 𝒰 F).X p :=
  (alternatingCechInclusion 𝒰 F).f p ≫ cechProjectionToOrderedCechComponent 𝒰 F p

@[simp] theorem alternatingCechProjectionComponent_f_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (alternatingCechComplex 𝒰 F).X p) (σ : StrictCechTuple p) :
    alternatingCechProjectionComponent 𝒰 F p s σ = s.1 σ := sorry

theorem alternatingCechProjectionComponent_comm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    alternatingCechProjectionComponent 𝒰 F p ≫ (orderedCechComplex 𝒰 F).d p (p + 1) =
      (alternatingCechComplex 𝒰 F).d p (p + 1) ≫
        alternatingCechProjectionComponent 𝒰 F (p + 1) := by
  calc
    alternatingCechProjectionComponent 𝒰 F p ≫ (orderedCechComplex 𝒰 F).d p (p + 1) =
        (alternatingCechInclusion 𝒰 F).f p ≫
          (cechProjectionToOrderedCechComponent 𝒰 F p ≫
            (orderedCechComplex 𝒰 F).d p (p + 1)) := by
          simp [alternatingCechProjectionComponent, Category.assoc]
    _ =
        (alternatingCechInclusion 𝒰 F).f p ≫
          (((cechComplexFunctor 𝒰).obj F).d p (p + 1) ≫
            cechProjectionToOrderedCechComponent 𝒰 F (p + 1)) := by
          rw [cechProjectionToOrderedCechComponent_comm]
    _ =
        ((alternatingCechInclusion 𝒰 F).f p ≫
          ((cechComplexFunctor 𝒰).obj F).d p (p + 1)) ≫
            cechProjectionToOrderedCechComponent 𝒰 F (p + 1) := by
          simp [Category.assoc]
    _ =
        (alternatingCechComplex 𝒰 F).d p (p + 1) ≫
          (alternatingCechInclusion 𝒰 F).f (p + 1) ≫
            cechProjectionToOrderedCechComponent 𝒰 F (p + 1) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ cechProjectionToOrderedCechComponent 𝒰 F (p + 1))
              ((alternatingCechInclusion 𝒰 F).comm p (p + 1))
    _ =
        (alternatingCechComplex 𝒰 F).d p (p + 1) ≫
          alternatingCechProjectionComponent 𝒰 F (p + 1) := by
          simp [alternatingCechProjectionComponent]

@[simp] theorem orderedCechComparisonComponent_comp_alternatingCechProjectionComponent
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechComparisonComponent 𝒰 F p ≫ alternatingCechProjectionComponent 𝒰 F p = 𝟙 _ := by
  ext s
  funext σ
  change alternatingCechProjectionComponent 𝒰 F p
      (orderedCechComparisonComponent 𝒰 F p s) σ = s σ
  rw [alternatingCechProjectionComponent_f_apply]
  exact orderedCechComparisonToFun_apply_strict 𝒰 F p s σ

@[simp] theorem alternatingCechProjectionComponent_comp_orderedCechComparisonComponent
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    alternatingCechProjectionComponent 𝒰 F p ≫ orderedCechComparisonComponent 𝒰 F p = 𝟙 _ := by
  ext s
  apply Subtype.ext
  funext σ
  change orderedCechComparisonToFun 𝒰 F p (alternatingCechProjectionComponent 𝒰 F p s) σ =
    s.1 σ
  have hs : alternatingCechProjectionComponent 𝒰 F p s =
      ((fun τ ↦ s.1 τ) : (orderedCechComplex 𝒰 F).X p) := by
    funext τ
    exact alternatingCechProjectionComponent_f_apply 𝒰 F p s τ
  rw [hs]
  exact congrFun (orderedCechComparisonToFun_eq_of_alternating 𝒰 F p s) σ

theorem orderedCechComparisonComponent_comm (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    orderedCechComparisonComponent 𝒰 F p ≫ (alternatingCechComplex 𝒰 F).d p (p + 1) =
      (orderedCechComplex 𝒰 F).d p (p + 1) ≫
        orderedCechComparisonComponent 𝒰 F (p + 1) := sorry

/-- The canonical comparison morphism
`c : orderedCechComplex 𝒰 F ⟶ alternatingCechComplex 𝒰 F`. -/
def orderedCechComparison (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    orderedCechComplex 𝒰 F ⟶ alternatingCechComplex 𝒰 F :=
  HomologicalComplex.Hom.mk
    (orderedCechComparisonComponent 𝒰 F)
    (fun i j hij ↦ by
      rcases hij with rfl
      simpa using orderedCechComparisonComponent_comm 𝒰 F i)

/-- On an injective Čech tuple, the ordered-to-alternating comparison sorts the tuple and inserts
the sign of the sorting permutation. -/
theorem orderedCechComparison_f_apply_of_injective (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (orderedCechComplex 𝒰 F).X p) (σ : Fin (p + 1) → ι) (hσ : Function.Injective σ) :
    (TopCat.Presheaf.Cech.termIso 𝒰 F p).hom
        ((alternatingCechInclusion 𝒰 F).f p ((orderedCechComparison 𝒰 F).f p s)) σ =
      Equiv.Perm.sign (Tuple.sort σ) •
        F.map (eqToHom (cechIntersection_sortedStrictCechTupleOfInjective 𝒰 σ hσ).symm).op
          (s (sortedStrictCechTupleOfInjective σ hσ)) := sorry

/-- On a Čech tuple with repeated indices, the ordered-to-alternating comparison vanishes. -/
theorem orderedCechComparison_f_apply_of_not_injective (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (orderedCechComplex 𝒰 F).X p) (σ : Fin (p + 1) → ι)
    (hσ : ¬ Function.Injective σ) :
    (TopCat.Presheaf.Cech.termIso 𝒰 F p).hom
        ((alternatingCechInclusion 𝒰 F).f p ((orderedCechComparison 𝒰 F).f p s)) σ = 0 := sorry

/-- Lemma 20.23.4 (1): projection to strictly increasing multi-indices defines
`π : (cechComplexFunctor 𝒰).obj F ⟶ orderedCechComplex 𝒰 F`
as a morphism of complexes. -/
@[stacks 01FK]
def cechProjectionToOrderedCech (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    (cechComplexFunctor 𝒰).obj F ⟶ orderedCechComplex 𝒰 F :=
  HomologicalComplex.Hom.mk
    (cechProjectionToOrderedCechComponent 𝒰 F)
    (fun i j hij ↦ by
      rcases hij with rfl
      simpa using cechProjectionToOrderedCechComponent_comm 𝒰 F i)

@[simp] theorem cechProjectionToOrderedCech_f_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : ((cechComplexFunctor 𝒰).obj F).X p) (σ : StrictCechTuple p) :
    (cechProjectionToOrderedCech 𝒰 F).f p s σ =
      (TopCat.Presheaf.Cech.termIso 𝒰 F p).hom s σ := by
  rfl

/-- The projection
`π : alternatingCechComplex 𝒰 F ⟶ orderedCechComplex 𝒰 F` obtained by first including
alternating Čech cochains into the ordinary Čech complex and then restricting to strictly
increasing tuples. -/
abbrev alternatingCechProjection (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    alternatingCechComplex 𝒰 F ⟶ orderedCechComplex 𝒰 F :=
  alternatingCechInclusion 𝒰 F ≫ cechProjectionToOrderedCech 𝒰 F

@[simp] theorem alternatingCechProjection_f_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (alternatingCechComplex 𝒰 F).X p) (σ : StrictCechTuple p) :
    (alternatingCechProjection 𝒰 F).f p s σ = s.1 σ := sorry

/-- The projection `π` from alternating to ordered Čech cochains is a left inverse to the
comparison morphism `c`. -/
@[simp] theorem alternatingCechProjection_comp_orderedCechComparison
    (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    alternatingCechProjection 𝒰 F ≫ orderedCechComparison 𝒰 F = 𝟙 _ := by
  ext p s
  apply Subtype.ext
  funext σ
  change orderedCechComparisonToFun 𝒰 F p ((alternatingCechProjection 𝒰 F).f p s) σ = s.1 σ
  have hs : (alternatingCechProjection 𝒰 F).f p s =
      ((fun τ ↦ s.1 τ) : (orderedCechComplex 𝒰 F).X p) := by
    funext τ
    exact alternatingCechProjection_f_apply 𝒰 F p s τ
  rw [hs]
  exact congrFun (orderedCechComparisonToFun_eq_of_alternating 𝒰 F p s) σ

-- Proof sketch: applying `c` first extends an ordered cochain by the signed permutation rule, and
-- restricting back with `π` recovers the original ordered coordinates.
/-- Lemma 20.23.4 (3): after extending an ordered Čech cochain by the signed-sorting formula,
restricting back to strictly increasing tuples recovers the original ordered cochain. -/
@[simp] theorem orderedCechComparison_comp_alternatingCechProjection (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    orderedCechComparison 𝒰 F ≫ alternatingCechProjection 𝒰 F = 𝟙 _ := by
  ext p s
  funext σ
  change (alternatingCechProjection 𝒰 F).f p ((orderedCechComparison 𝒰 F).f p s) σ = s σ
  rw [alternatingCechProjection_f_apply]
  exact orderedCechComparisonToFun_apply_strict 𝒰 F p s σ

@[simp] theorem orderedCechComparison_f_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (orderedCechComplex 𝒰 F).X p) (σ : StrictCechTuple p) :
    (TopCat.Presheaf.Cech.termIso 𝒰 F p).hom
        ((alternatingCechInclusion 𝒰 F).f p ((orderedCechComparison 𝒰 F).f p s)) σ =
      s σ := by
  simpa [alternatingCechProjection] using
    (show (alternatingCechProjection 𝒰 F).f p ((orderedCechComparison 𝒰 F).f p s) σ = s σ from by
      rw [alternatingCechProjection_f_apply]
      exact orderedCechComparisonToFun_apply_strict 𝒰 F p s σ)

-- Proof sketch: the ordered complex and the alternating subcomplex are identified by the explicit
-- comparison maps `c` and `π`, which undo each other on strictly increasing tuples.
/-- Lemma 20.23.4 (2): the restriction of `π` to alternating Čech cochains is an isomorphism of
complexes onto the ordered Čech complex. -/
@[stacks 01FK]
instance alternatingCechProjection_isIso (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    IsIso (alternatingCechProjection 𝒰 F) := by
  exact ⟨⟨orderedCechComparison 𝒰 F,
    alternatingCechProjection_comp_orderedCechComparison 𝒰 F,
    orderedCechComparison_comp_alternatingCechProjection 𝒰 F⟩⟩
