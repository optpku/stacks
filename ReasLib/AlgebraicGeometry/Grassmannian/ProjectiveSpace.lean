/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Grassmannian.Model
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Datum
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Representability

/-!
# Rank-one Grassmannian quotients and projective space

Rank-one quotients of a free module sheaf correspond naturally to invertible module sheaves
equipped with a generating family of sections.  This identifies the Grassmannian functor in
successive dimensions with the projective-space datum functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Grassmannian.Quotient

/-- A quotient of a free module of rank `n + 1` with Grassmannian index `n` has an invertible
target module. -/
theorem selfSucc_isInvertible (n : ℕ) {S : Scheme.{u}}
    (Q : Grassmannian.Quotient n (n + 1) S) :
    Scheme.Modules.Invertible Q.module := sorry

set_option backward.isDefEq.respectTransparency false in
/-- The sections induced by a rank-one Grassmannian quotient generate its target module. -/
theorem selfSucc_sectionFamilyHom_epi (n : ℕ) {S : Scheme.{u}}
    (Q : Grassmannian.Quotient n (n + 1) S) :
    Epi (ProjectiveSpaceDatum.sectionFamilyHom Q.module n
      (fun i ↦ Q.module.freeHomEquiv Q.map (ULift.up i))) := by
  simpa only [ProjectiveSpaceDatum.sectionFamilyHom, ULift.up_down,
    Equiv.symm_apply_apply] using Q.map_epi

/-- A rank-one Grassmannian quotient determines an invertible module with `n + 1` generating
sections. -/
def toProjectiveSpaceDatum (n : ℕ) {S : Scheme.{u}}
    (Q : Grassmannian.Quotient n (n + 1) S) : ProjectiveSpaceDatum n S where
  lineBundle := Q.module
  invertible_lineBundle := selfSucc_isInvertible n Q
  sections := fun i ↦ Q.module.freeHomEquiv Q.map (ULift.up i)
  generates := selfSucc_sectionFamilyHom_epi n Q

/-- Compatible isomorphisms of rank-one Grassmannian quotients induce equivalent
projective-space data. -/
theorem rel_toProjectiveSpaceDatum (n : ℕ) {S : Scheme.{u}}
    {Q Q' : Grassmannian.Quotient n (n + 1) S} :
    Rel Q Q' →
      ProjectiveSpaceDatum.Equivalent
        (toProjectiveSpaceDatum n Q) (toProjectiveSpaceDatum n Q') := by
  rintro ⟨e, he⟩
  refine ⟨e, fun i ↦ ?_⟩
  change SheafOfModules.sectionsMap e.hom (Q.module.freeHomEquiv Q.map (ULift.up i)) =
    Q'.module.freeHomEquiv Q'.map (ULift.up i)
  rw [← SheafOfModules.freeHomEquiv_comp_apply, he]

set_option backward.isDefEq.respectTransparency false in
/-- Conversion of a rank-one Grassmannian quotient to projective-space data commutes with
pullback up to the defining equivalence of projective-space data. -/
theorem toProjectiveSpaceDatum_pullback_equivalent (n : ℕ) {S T : Scheme.{u}}
    (f : T ⟶ S) (Q : Grassmannian.Quotient n (n + 1) S) :
    ProjectiveSpaceDatum.Equivalent
      (toProjectiveSpaceDatum n (pullback f Q))
      (ProjectiveSpaceDatum.pullback f (toProjectiveSpaceDatum n Q)) := by
  letI : (TopologicalSpace.Opens.map f.base).Final :=
    CategoryTheory.final_of_representablyFlat (TopologicalSpace.Opens.map f.base)
  refine ⟨Iso.refl _, fun i ↦ ?_⟩
  let φ := f.toRingCatSheafHom
  let e := SheafOfModules.pullbackObjFreeIso φ (ULift.{u} (Fin (n + 1)))
  let ε := asIso (SheafOfModules.pullbackObjUnitToUnit φ)
  have he : (SheafOfModules.pullback φ).map (SheafOfModules.ιFree (ULift.up i)) ≫ e.hom =
      ε.hom ≫ SheafOfModules.ιFree (ULift.up i) :=
    SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom φ (ULift.up i)
  have h : SheafOfModules.ιFree (ULift.up i) ≫ e.inv =
      ε.inv ≫ (SheafOfModules.pullback φ).map (SheafOfModules.ιFree (ULift.up i)) := by
    apply (cancel_mono e.hom).1
    simp only [Category.assoc, he, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  change ((SheafOfModules.pullback φ).obj Q.module).unitHomEquiv
    (SheafOfModules.ιFree (ULift.up i) ≫ e.inv ≫ (SheafOfModules.pullback φ).map Q.map) =
      Scheme.Modules.sectionsPullback f Q.module (Q.module.freeHomEquiv Q.map (ULift.up i))
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp,
    ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  let s := Q.module.freeHomEquiv Q.map (ULift.up i)
  let adj := SheafOfModules.pullbackPushforwardAdjunction φ
  let t := Q.module.unitHomEquiv.symm s
  have hs : SheafOfModules.pushforwardSections φ
      (Scheme.Modules.sectionsPullback f Q.module s) =
      SheafOfModules.sectionsMap (adj.unit.app Q.module) s := by
    apply (RingedSpace.sectionsEquivTop _).injective
    change (((Scheme.Modules.pullback f).obj Q.module).presheaf.map (𝟙 _)) _ = _
    simp
    rfl
  symm
  apply (SheafOfModules.bijective_pushforwardSections φ _).injective
  rw [hs]
  refine Eq.trans ?_ (SheafOfModules.pushforwardSections_unitHomEquiv φ
    (M := (SheafOfModules.pullback φ).obj Q.module)
    (ε.inv ≫ (SheafOfModules.pullback φ).map t)).symm
  change SheafOfModules.sectionsMap (adj.unit.app Q.module) s =
    ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj Q.module)).unitHomEquiv
      (SheafOfModules.unitToPushforwardObjUnit φ ≫
        (Scheme.Modules.pushforward f).map (ε.inv ≫ (Scheme.Modules.pullback f).map t))
  have ht : SheafOfModules.unitToPushforwardObjUnit φ ≫
      (Scheme.Modules.pushforward f).map (ε.inv ≫ (Scheme.Modules.pullback f).map t) =
      t ≫ adj.unit.app Q.module := by
    calc
      _ = adj.homEquiv _ _ (ε.hom ≫ ε.inv ≫ (Scheme.Modules.pullback f).map t) := by
        rw [Adjunction.homEquiv_naturality_right]
        change _ = (SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv _ _
          (SheafOfModules.pullbackObjUnitToUnit φ) ≫ _
        rw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
        rfl
      _ = t ≫ adj.unit.app Q.module := by
        simp only [Iso.hom_inv_id_assoc]
        rw [Adjunction.homEquiv_unit, ← adj.unit_naturality]
        rfl
  rw [ht, SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]

end Grassmannian.Quotient

namespace ProjectiveSpaceDatum

/-- The line bundle of projective-space data has the rank required for a quotient of a free
module of rank `n + 1` with Grassmannian index `n`. -/
theorem isFiniteLocallyFreeOfRank_selfSucc (n : ℕ) {S : Scheme.{u}}
    (τ : ProjectiveSpaceDatum n S) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank ((n + 1) - n) τ.lineBundle := sorry

/-- An invertible module with `n + 1` generating sections determines a rank-one Grassmannian
quotient. -/
def toGrassmannianQuotient (n : ℕ) {S : Scheme.{u}}
    (τ : ProjectiveSpaceDatum n S) : Grassmannian.Quotient n (n + 1) S where
  module := τ.lineBundle
  isLocallyFree := isFiniteLocallyFreeOfRank_selfSucc n τ
  map := sectionFamilyHom τ.lineBundle n τ.sections
  map_epi := τ.generates

set_option backward.isDefEq.respectTransparency false in
/-- Equivalent projective-space data determine related rank-one Grassmannian quotients. -/
theorem equivalent_toGrassmannianQuotient (n : ℕ) {S : Scheme.{u}}
    {τ τ' : ProjectiveSpaceDatum n S} :
    Equivalent τ τ' →
      Grassmannian.Quotient.Rel
        (toGrassmannianQuotient n τ) (toGrassmannianQuotient n τ') := by
  rintro ⟨e, he⟩
  refine ⟨e, ?_⟩
  change sectionFamilyHom τ.lineBundle n τ.sections ≫ e.hom =
    sectionFamilyHom τ'.lineBundle n τ'.sections
  apply τ'.lineBundle.freeHomEquiv.injective
  funext i
  rw [SheafOfModules.freeHomEquiv_comp_apply]
  simpa only [sectionFamilyHom, Equiv.apply_symm_apply] using he i.down

end ProjectiveSpaceDatum

namespace Grassmannian.Quotient

/-- Passing from a rank-one Grassmannian quotient to projective-space data and back preserves
its Grassmannian quotient class. -/
theorem toProjectiveSpaceDatum_toGrassmannianQuotient_rel (n : ℕ) {S : Scheme.{u}}
    (Q : Grassmannian.Quotient n (n + 1) S) :
    Rel (ProjectiveSpaceDatum.toGrassmannianQuotient n
      (toProjectiveSpaceDatum n Q)) Q := by
  refine ⟨Iso.refl _, ?_⟩
  change ProjectiveSpaceDatum.sectionFamilyHom Q.module n
    (fun i ↦ Q.module.freeHomEquiv Q.map (ULift.up i)) ≫ 𝟙 _ = Q.map
  simp only [ProjectiveSpaceDatum.sectionFamilyHom, ULift.up_down,
    Equiv.symm_apply_apply, Category.comp_id]

end Grassmannian.Quotient

namespace ProjectiveSpaceDatum

/-- Passing from projective-space data to a rank-one Grassmannian quotient and back preserves
its projective-space datum class. -/
theorem toGrassmannianQuotient_toProjectiveSpaceDatum_equivalent
    (n : ℕ) {S : Scheme.{u}} (τ : ProjectiveSpaceDatum n S) :
    Equivalent
      (Grassmannian.Quotient.toProjectiveSpaceDatum n
        (toGrassmannianQuotient n τ)) τ := by
  refine ⟨Iso.refl _, fun i ↦ ?_⟩
  change τ.lineBundle.freeHomEquiv
    (sectionFamilyHom τ.lineBundle n τ.sections) (ULift.up i) = τ.sections i
  simp only [sectionFamilyHom, Equiv.apply_symm_apply]

end ProjectiveSpaceDatum

namespace Grassmannian

/-- Send a rank-one Grassmannian quotient class to its projective-space datum class. -/
def toProjectiveSpaceDatumClass (n : ℕ) {S : Scheme.{u}} :
    (functor n (n + 1)).obj (Opposite.op S) → ProjectiveSpaceDatumClass n S :=
  _root_.Quotient.map (Quotient.toProjectiveSpaceDatum n)
    (fun {_ _} h ↦ Quotient.rel_toProjectiveSpaceDatum n h)

/-- Send a projective-space datum class to its rank-one Grassmannian quotient class. -/
def ofProjectiveSpaceDatumClass (n : ℕ) {S : Scheme.{u}} :
    ProjectiveSpaceDatumClass n S → (functor n (n + 1)).obj (Opposite.op S) :=
  _root_.Quotient.map (ProjectiveSpaceDatum.toGrassmannianQuotient n)
    (fun {_ _} h ↦ ProjectiveSpaceDatum.equivalent_toGrassmannianQuotient n h)

/-- Converting a Grassmannian class to a projective-space datum class and back is the identity.
-/
theorem ofProjectiveSpaceDatumClass_toProjectiveSpaceDatumClass
    (n : ℕ) {S : Scheme.{u}} (Q : (functor n (n + 1)).obj (Opposite.op S)) :
    ofProjectiveSpaceDatumClass n (toProjectiveSpaceDatumClass n Q) = Q := by
  refine _root_.Quotient.inductionOn Q ?_
  intro Q
  exact _root_.Quotient.sound
    (Quotient.toProjectiveSpaceDatum_toGrassmannianQuotient_rel n Q)

/-- Converting a projective-space datum class to a Grassmannian class and back is the identity.
-/
theorem toProjectiveSpaceDatumClass_ofProjectiveSpaceDatumClass
    (n : ℕ) {S : Scheme.{u}} (τ : ProjectiveSpaceDatumClass n S) :
    toProjectiveSpaceDatumClass n (ofProjectiveSpaceDatumClass n τ) = τ := by
  refine _root_.Quotient.inductionOn τ ?_
  intro τ
  exact _root_.Quotient.sound
    (ProjectiveSpaceDatum.toGrassmannianQuotient_toProjectiveSpaceDatum_equivalent n τ)

/-- Rank-one Grassmannian quotient classes are equivalent to projective-space datum classes. -/
def selfSuccDatumClassEquiv (n : ℕ) (S : Scheme.{u}) :
    (functor n (n + 1)).obj (Opposite.op S) ≃ ProjectiveSpaceDatumClass n S where
  toFun := toProjectiveSpaceDatumClass n
  invFun := ofProjectiveSpaceDatumClass n
  left_inv := ofProjectiveSpaceDatumClass_toProjectiveSpaceDatumClass n
  right_inv := toProjectiveSpaceDatumClass_ofProjectiveSpaceDatumClass n

/-- The equivalence between rank-one quotient classes and projective-space datum classes is
natural under pullback of schemes. -/
theorem selfSuccDatumClassEquiv_naturality (n : ℕ) {S T : Scheme.{u}ᵒᵖ}
    (f : S ⟶ T) :
    (functor n (n + 1)).map f ≫
        (selfSuccDatumClassEquiv n T.unop).toIso.hom =
      (selfSuccDatumClassEquiv n S.unop).toIso.hom ≫
        (ProjectiveSpaceDatumClass.functor n).map f := by
  ext Q
  refine _root_.Quotient.inductionOn Q ?_
  intro Q
  exact _root_.Quotient.sound
    (Quotient.toProjectiveSpaceDatum_pullback_equivalent n f.unop Q)

/-- The Grassmannian functor in successive dimensions is naturally isomorphic to the functor
of projective-space data. -/
def selfSuccFunctorIso (n : ℕ) :
    functor.{u} n (n + 1) ≅ ProjectiveSpaceDatumClass.functor.{u} n :=
  NatIso.ofComponents
    (fun S ↦ (selfSuccDatumClassEquiv n S.unop).toIso)
    (fun f ↦ selfSuccDatumClassEquiv_naturality n f)

namespace Model

/-- Comparison with projective space using its canonical coordinate datum.
The supplied inverse bijections must be normalized at `(O(1), T_0, ..., T_n)`.
They remain explicit inputs: extracting them from the unproved representability
proposition would introduce a data dependency on that proof. -/
def selfSuccIsoProjectiveSpace (n : ℕ) (hn : 0 < n)
    (P : Model n (n + 1) hn (Nat.lt_succ_self n))
    (R : (ProjectiveSpaceDatumClass.functor n).RepresentableBy
      (ProjectiveSpace.scheme ℤ n))
    (_hR : R.homEquiv (𝟙 _) = ProjectiveSpaceDatumClass.universalClass n) :
    P.scheme ≅ ProjectiveSpace.scheme ℤ n :=
  (P.isRepresentedBy.representableBy.ofIso (selfSuccFunctorIso n)).uniqueUpToIso R

/-- The forward morphism of the comparison isomorphism classifies the projective-space datum
obtained from the universal rank-one quotient. -/
theorem selfSuccIsoProjectiveSpace_hom_classifies (n : ℕ) (hn : 0 < n)
    (P : Model n (n + 1) hn (Nat.lt_succ_self n))
    (R : (ProjectiveSpaceDatumClass.functor n).RepresentableBy
      (ProjectiveSpace.scheme ℤ n))
    (hR : R.homEquiv (𝟙 _) = ProjectiveSpaceDatumClass.universalClass n) :
    (ProjectiveSpaceDatumClass.functor n).map
        (selfSuccIsoProjectiveSpace n hn P R hR).hom.op
        (ProjectiveSpaceDatumClass.universalClass n) =
      (selfSuccFunctorIso n).hom.app (Opposite.op P.scheme) P.point := by
  rw [← hR, ← R.homEquiv_eq]
  change R.homEquiv (R.homEquiv.symm
    ((selfSuccFunctorIso n).hom.app (Opposite.op P.scheme)
      (P.isRepresentedBy.representableBy.homEquiv (𝟙 P.scheme)))) = _
  rw [Equiv.apply_symm_apply, Functor.IsRepresentedBy.representableBy_homEquiv_apply]
  simp

/-- Normalization at the canonical coordinate datum makes the comparison independent of
the supplied representation and its normalization proof. -/
theorem selfSuccIsoProjectiveSpace_eq (n : ℕ) (hn : 0 < n)
    (P : Model n (n + 1) hn (Nat.lt_succ_self n))
    (R R' : (ProjectiveSpaceDatumClass.functor n).RepresentableBy
      (ProjectiveSpace.scheme ℤ n))
    (hR : R.homEquiv (𝟙 _) = ProjectiveSpaceDatumClass.universalClass n)
    (hR' : R'.homEquiv (𝟙 _) = ProjectiveSpaceDatumClass.universalClass n) :
    selfSuccIsoProjectiveSpace n hn P R hR =
      selfSuccIsoProjectiveSpace n hn P R' hR' := by
  apply Iso.ext
  apply R.homEquiv.injective
  conv_lhs => rw [R.homEquiv_eq, hR]
  conv_rhs => rw [R.homEquiv_eq, hR]
  rw [selfSuccIsoProjectiveSpace_hom_classifies,
    selfSuccIsoProjectiveSpace_hom_classifies]

/-- The canonical comparison is the unique isomorphism pulling back the coordinate datum
to the datum of the universal rank-one quotient. This statement needs no supplied
projective-space representation. It asserts existence in `Prop` and does not choose
isomorphism data from the admitted representability law. -/
theorem existsUnique_selfSuccIsoProjectiveSpace (n : ℕ) (hn : 0 < n)
    (P : Model n (n + 1) hn (Nat.lt_succ_self n)) :
    ∃! e : P.scheme ≅ ProjectiveSpace.scheme ℤ n,
      (ProjectiveSpaceDatumClass.functor n).map e.hom.op
          (ProjectiveSpaceDatumClass.universalClass n) =
        (selfSuccFunctorIso n).hom.app (Opposite.op P.scheme) P.point := by
  obtain ⟨R, hR⟩ := Functor.IsRepresentedBy.iff_exists_representableBy.mp
    (ProjectiveSpaceDatumClass.universalClass_isRepresentedBy n)
  refine ⟨selfSuccIsoProjectiveSpace n hn P R hR,
    selfSuccIsoProjectiveSpace_hom_classifies n hn P R hR, ?_⟩
  intro e he
  apply Iso.ext
  apply R.homEquiv.injective
  conv_lhs => rw [R.homEquiv_eq, hR]
  conv_rhs => rw [R.homEquiv_eq, hR]
  exact he.trans (selfSuccIsoProjectiveSpace_hom_classifies n hn P R hR).symm

end Model

end Grassmannian

end AlgebraicGeometry
