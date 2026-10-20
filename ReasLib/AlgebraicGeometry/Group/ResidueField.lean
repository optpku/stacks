module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Section
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.ResidueField
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Residue fields at the identity of a group scheme

This file records point and residue-field identities for multiplication and the unit section of
a group object in schemes over a base.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Pullback

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.GroupTangent

/-- The structure morphism of a group scheme induces a bijection on residue fields at the value
of the identity section over a base point. -/
theorem unit_residueFieldMap_bijective
    {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S) :
    Function.Bijective (G.hom.residueFieldMap (η[G].left s)).hom := by
  -- Specialize the split-morphism residue-field lemma to the identity section of the group
  -- object over `S`.
  exact AlgebraicGeometry.Scheme.Hom.residueFieldMap_bijective_of_section
    (e := η[G].left) (f := G.hom) (hsec := Over.w η[G]) (y := s)

/-- The explicit pair of identity points agrees with the canonical pullback point selected by the
two identity-section residue-field identifications. -/
theorem unitPair_eq_selected
    {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S) :
    (lift η[G] η[G]).left s =
      pointOfBaseResidueFieldMapBijective G.hom G.hom
        (η[G].left s) (η[G].left s) rfl
        (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s) := by
  -- Local instance justification (proof-local temporary data): the pullback-point uniqueness theorem requires this IsIso induced by the proved residue-field bijection.
  letI : IsIso (G.hom.residueFieldMap (η[G].left s)) :=
    (RingEquiv.ofBijective (G.hom.residueFieldMap (η[G].left s)).hom
      (unit_residueFieldMap_bijective G s)).toCommRingCatIso.isIso_hom
  obtain ⟨p, hp, hp_unique⟩ :=
    existsUnique_point_of_rightResidueFieldIso
      G.hom G.hom (η[G].left s) (η[G].left s) rfl
  have hunit_fst :
      pullback.fst G.hom G.hom ((lift η[G] η[G]).left s) = η[G].left s := by
    -- The explicit identity pair projects to the identity point in the first factor.
    have hproj_fst :
        pullback.lift (η[G].left) (η[G].left) rfl ≫ pullback.fst G.hom G.hom = η[G].left :=
      pullback.lift_fst (f := G.hom) (g := G.hom)
        (h := η[G].left) (k := η[G].left) (w := rfl)
    change
      TopCat.Hom.hom (pullback.fst G.hom G.hom).base
          (TopCat.Hom.hom ((lift η[G] η[G]).left).base s) =
        TopCat.Hom.hom (η[G].left).base s
    exact congrArg (fun k : S ⟶ G.left ↦ TopCat.Hom.hom k.base s) hproj_fst
  have hunit_snd :
      pullback.snd G.hom G.hom ((lift η[G] η[G]).left s) = η[G].left s := by
    -- The same explicit point projects to the identity point in the second factor as well.
    have hproj_snd :
        pullback.lift (η[G].left) (η[G].left) rfl ≫ pullback.snd G.hom G.hom = η[G].left :=
      pullback.lift_snd (f := G.hom) (g := G.hom)
        (h := η[G].left) (k := η[G].left) (w := rfl)
    change
      TopCat.Hom.hom (pullback.snd G.hom G.hom).base
          (TopCat.Hom.hom ((lift η[G] η[G]).left).base s) =
        TopCat.Hom.hom (η[G].left).base s
    exact congrArg (fun k : S ⟶ G.left ↦ TopCat.Hom.hom k.base s) hproj_snd
  have hselected :
      pullback.fst G.hom G.hom
          (pointOfBaseResidueFieldMapBijective G.hom G.hom
            (η[G].left s) (η[G].left s) rfl
            (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)) =
        η[G].left s ∧
      pullback.snd G.hom G.hom
          (pointOfBaseResidueFieldMapBijective G.hom G.hom
            (η[G].left s) (η[G].left s) rfl
            (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)) =
        η[G].left s := by
    constructor
    · exact pointOfBaseResidueFieldMapBijective_fst
        G.hom G.hom (η[G].left s) (η[G].left s) rfl
          (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)
    · exact pointOfBaseResidueFieldMapBijective_snd
        G.hom G.hom (η[G].left s) (η[G].left s) rfl
          (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)
  -- Both points have the same projections, so uniqueness in the pullback identifies them.
  exact (hp_unique _ ⟨hunit_fst, hunit_snd⟩).trans (hp_unique _ hselected).symm

/-- Evaluating the right-unit section at the identity point yields the explicit unit pair. -/
theorem rightUnitSection_apply_eq_unitPair
    {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S) :
    (lift (𝟙 G) (toUnit G ≫ η[G])).left (η[G].left s) = (lift η[G] η[G]).left s := by
  -- Local instance justification (proof-local temporary data): the pullback-point uniqueness theorem requires this IsIso induced by the proved residue-field bijection.
  letI : IsIso (G.hom.residueFieldMap (η[G].left s)) :=
    (RingEquiv.ofBijective (G.hom.residueFieldMap (η[G].left s)).hom
      (unit_residueFieldMap_bijective G s)).toCommRingCatIso.isIso_hom
  obtain ⟨p, hp, hp_unique⟩ :=
    existsUnique_point_of_rightResidueFieldIso
      G.hom G.hom (η[G].left s) (η[G].left s) rfl
  have hs :
      TopCat.Hom.hom G.hom.base (TopCat.Hom.hom (η[G].left).base s) = s := by
    -- Evaluating the identity-section equation fixes the base point of the unit section.
    exact congrArg (fun k : S ⟶ S ↦ TopCat.Hom.hom k.base s) (Over.w η[G])
  have hraw_fst :
      pullback.fst G.hom G.hom
          ((lift (𝟙 G) (toUnit G ≫ η[G])).left (η[G].left s)) =
        η[G].left s := by
    have hproj :
        pullback.lift (𝟙 G.left) ((toUnit G ≫ η[G]).left)
            (by simpa using (Over.w (toUnit G ≫ η[G])).symm) ≫
          pullback.fst G.hom G.hom =
        𝟙 G.left := by
      -- The first projection of the right-unit section is the identity on `G`.
      exact pullback.lift_fst (f := G.hom) (g := G.hom)
        (h := 𝟙 G.left) (k := (toUnit G ≫ η[G]).left)
        (w := by simpa using (Over.w (toUnit G ≫ η[G])).symm)
    change
      TopCat.Hom.hom (pullback.fst G.hom G.hom).base
          (TopCat.Hom.hom ((lift (𝟙 G) (toUnit G ≫ η[G])).left).base (η[G].left s)) =
        η[G].left s
    exact congrArg (fun k : G.left ⟶ G.left ↦ TopCat.Hom.hom k.base (η[G].left s)) hproj
  have hraw_snd :
      pullback.snd G.hom G.hom
          ((lift (𝟙 G) (toUnit G ≫ η[G])).left (η[G].left s)) =
        η[G].left s := by
    have hproj :
        pullback.lift (𝟙 G.left) ((toUnit G ≫ η[G]).left)
            (by simpa using (Over.w (toUnit G ≫ η[G])).symm) ≫
          pullback.snd G.hom G.hom =
        (toUnit G ≫ η[G]).left := by
      -- The second projection records the unit section after the structure morphism.
      exact pullback.lift_snd (f := G.hom) (g := G.hom)
        (h := 𝟙 G.left) (k := (toUnit G ≫ η[G]).left)
        (w := by simpa using (Over.w (toUnit G ≫ η[G])).symm)
    have hsnd_eval :
        (toUnit G ≫ η[G]).left (η[G].left s) = η[G].left s := by
      -- The composite `G ⟶ S ⟶ G` sends the identity point back to itself.
      exact congrArg (fun t : S ↦ η[G].left t) hs
    exact
      (congrArg (fun k : G.left ⟶ G.left ↦ TopCat.Hom.hom k.base (η[G].left s)) hproj).trans
        hsnd_eval
  have hselected :
      pullback.fst G.hom G.hom
          (pointOfBaseResidueFieldMapBijective G.hom G.hom
            (η[G].left s) (η[G].left s) rfl
            (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)) =
        η[G].left s ∧
      pullback.snd G.hom G.hom
          (pointOfBaseResidueFieldMapBijective G.hom G.hom
            (η[G].left s) (η[G].left s) rfl
            (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)) =
        η[G].left s := by
    constructor
    · exact pointOfBaseResidueFieldMapBijective_fst
        G.hom G.hom (η[G].left s) (η[G].left s) rfl
          (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)
    · exact pointOfBaseResidueFieldMapBijective_snd
        G.hom G.hom (η[G].left s) (η[G].left s) rfl
          (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)
  -- Both points have the same two pullback projections, so uniqueness identifies them.
  exact
    ((hp_unique _ ⟨hraw_fst, hraw_snd⟩).trans (hp_unique _ hselected).symm).trans
      (unitPair_eq_selected G s).symm

/-- Evaluating the left-unit section at the identity point yields the explicit unit pair. -/
theorem leftUnitSection_apply_eq_unitPair
    {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S) :
    (lift (toUnit G ≫ η[G]) (𝟙 G)).left (η[G].left s) = (lift η[G] η[G]).left s := by
  -- Local instance justification (proof-local temporary data): the pullback-point uniqueness theorem requires this IsIso induced by the proved residue-field bijection.
  letI : IsIso (G.hom.residueFieldMap (η[G].left s)) :=
    (RingEquiv.ofBijective (G.hom.residueFieldMap (η[G].left s)).hom
      (unit_residueFieldMap_bijective G s)).toCommRingCatIso.isIso_hom
  obtain ⟨p, hp, hp_unique⟩ :=
    existsUnique_point_of_rightResidueFieldIso
      G.hom G.hom (η[G].left s) (η[G].left s) rfl
  have hs :
      TopCat.Hom.hom G.hom.base (TopCat.Hom.hom (η[G].left).base s) = s := by
    -- Evaluating the identity-section equation fixes the base point of the unit section.
    exact congrArg (fun k : S ⟶ S ↦ TopCat.Hom.hom k.base s) (Over.w η[G])
  have hraw_fst :
      pullback.fst G.hom G.hom
          ((lift (toUnit G ≫ η[G]) (𝟙 G)).left (η[G].left s)) =
        η[G].left s := by
    have hproj :
        pullback.lift ((toUnit G ≫ η[G]).left) (𝟙 G.left)
            (by simpa using (Over.w (toUnit G ≫ η[G]))) ≫
          pullback.fst G.hom G.hom =
        (toUnit G ≫ η[G]).left := by
      -- The first projection records the unit section after the structure morphism.
      exact pullback.lift_fst (f := G.hom) (g := G.hom)
        (h := (toUnit G ≫ η[G]).left) (k := 𝟙 G.left)
        (w := by simpa using (Over.w (toUnit G ≫ η[G])))
    have hfst_eval :
        (toUnit G ≫ η[G]).left (η[G].left s) = η[G].left s := by
      -- The composite `G ⟶ S ⟶ G` sends the identity point back to itself.
      exact congrArg (fun t : S ↦ η[G].left t) hs
    exact
      (congrArg (fun k : G.left ⟶ G.left ↦ TopCat.Hom.hom k.base (η[G].left s)) hproj).trans
        hfst_eval
  have hraw_snd :
      pullback.snd G.hom G.hom
          ((lift (toUnit G ≫ η[G]) (𝟙 G)).left (η[G].left s)) =
        η[G].left s := by
    have hproj :
        pullback.lift ((toUnit G ≫ η[G]).left) (𝟙 G.left)
            (by simpa using (Over.w (toUnit G ≫ η[G]))) ≫
          pullback.snd G.hom G.hom =
        𝟙 G.left := by
      -- The second projection of the left-unit section is the identity on `G`.
      exact pullback.lift_snd (f := G.hom) (g := G.hom)
        (h := (toUnit G ≫ η[G]).left) (k := 𝟙 G.left)
        (w := by simpa using (Over.w (toUnit G ≫ η[G])))
    exact congrArg (fun k : G.left ⟶ G.left ↦ k (η[G].left s)) hproj
  have hselected :
      pullback.fst G.hom G.hom
          (pointOfBaseResidueFieldMapBijective G.hom G.hom
            (η[G].left s) (η[G].left s) rfl
            (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)) =
        η[G].left s ∧
      pullback.snd G.hom G.hom
          (pointOfBaseResidueFieldMapBijective G.hom G.hom
            (η[G].left s) (η[G].left s) rfl
            (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)) =
        η[G].left s := by
    constructor
    · exact pointOfBaseResidueFieldMapBijective_fst
        G.hom G.hom (η[G].left s) (η[G].left s) rfl
          (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)
    · exact pointOfBaseResidueFieldMapBijective_snd
        G.hom G.hom (η[G].left s) (η[G].left s) rfl
          (unit_residueFieldMap_bijective G s) (unit_residueFieldMap_bijective G s)
  -- Both points have the same two pullback projections, so uniqueness identifies them.
  exact
    ((hp_unique _ ⟨hraw_fst, hraw_snd⟩).trans (hp_unique _ hselected).symm).trans
      (unitPair_eq_selected G s).symm

/-- Multiplication sends the pair of identity points to the identity point. -/
theorem mul_unitPair {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S) :
    μ[G].left ((lift η[G] η[G]).left s) = η[G].left s := by
  -- Multiplying by the unit in the second factor is the identity morphism.
  have hmul : lift η[G] η[G] ≫ μ[G] = η[G] := by
    simpa using
      (CategoryTheory.MonObj.lift_comp_one_right
        (B := G) (f := η[G]) (g := 𝟙 (𝟙_ (Over S))))
  have hmul_left : (lift η[G] η[G]).left ≫ μ[G].left = η[G].left := by
    simpa using congrArg Over.Hom.left hmul
  exact congrArg (fun f : S ⟶ G.left ↦ f s) hmul_left

/-- Multiplication induces a bijection on residue fields at the pair of identity points. -/
theorem mul_residueFieldMap_bijective
    {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S) :
    Function.Bijective ((μ[G].left).residueFieldMap ((lift η[G] η[G]).left s)).hom := by
  have hsec_over : lift (𝟙 G) (toUnit G ≫ η[G]) ≫ μ[G] = 𝟙 G := by
    -- The right-unit section splits multiplication in `Over S`.
    simpa using
      (CategoryTheory.MonObj.lift_comp_one_right
        (B := G) (f := 𝟙 G) (g := toUnit G))
  have hsec :
      (lift (𝟙 G) (toUnit G ≫ η[G])).left ≫ μ[G].left = 𝟙 G.left := by
    -- Passing to the underlying scheme morphisms keeps the section identity.
    exact congrArg Over.Hom.left hsec_over
  -- After normalizing the section point to the explicit unit pair, the generic split-morphism
  -- residue-field lemma applies directly.
  rw [← rightUnitSection_apply_eq_unitPair G s]
  exact
    AlgebraicGeometry.Scheme.Hom.residueFieldMap_bijective_of_section
      (e := (lift (𝟙 G) (toUnit G ≫ η[G])).left)
      (f := μ[G].left) (hsec := hsec) (y := η[G].left s)

end AlgebraicGeometry.Scheme.GroupTangent
