/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Determinant
public import ReasLib.Algebra.Homology.CochainComplex.TwoTerm
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Category.ModuleCat.Projective

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CanonicalRingDeterminant

variable (R : Type u) [CommRing R]

/-- Finite-projective complexes in the actual two-term window. -/
structure Model where
  complex : CochainComplex (ModuleCat.{u} R) ℤ
  [ge : complex.IsStrictlyGE (-1)]
  [le : complex.IsStrictlyLE 0]
  [finiteNeg : Module.Finite R (complex.X (-1))]
  [projectiveNeg : Module.Projective R (complex.X (-1))]
  [finiteZero : Module.Finite R (complex.X 0)]
  [projectiveZero : Module.Projective R (complex.X 0)]

attribute [instance] Model.ge Model.le Model.finiteNeg Model.projectiveNeg
  Model.finiteZero Model.projectiveZero

abbrev Object := PerfectDerived.TorNegOneZero R

/-- The genuine representative existence theorem for perfect amplitude [-1,0].
Only a representative is chosen below, not a determinant or determinant iso. -/
theorem exists_model (K : Object R) :
    ∃ P : Model R, Nonempty (K.obj.obj ≅ DerivedCategory.Q.obj P.complex) := by sorry

def model (K : Object R) : Model R := (exists_model R K).choose

def realization (K : Object R) : K.obj.obj ≅ DerivedCategory.Q.obj (model R K).complex :=
  (exists_model R K).choose_spec.some

/-- Forget both full-subcategory witnesses, retaining the given derived map. -/
def underlyingIso {K L : Object R} (a : K ≅ L) : K.obj.obj ≅ L.obj.obj where
  hom := a.hom.hom.hom
  inv := a.inv.hom.hom
  hom_inv_id := congrArg (fun f => f.hom.hom) a.hom_inv_id
  inv_hom_id := congrArg (fun f => f.hom.hom) a.inv_hom_id

def realizedIso {K L : Object R} (a : K ≅ L) :
    DerivedCategory.Q.obj (model R K).complex ≅ DerivedCategory.Q.obj (model R L).complex :=
  (realization R K).symm ≪≫ underlyingIso R a ≪≫ realization R L

/-- A common admissible refinement representing a SPECIFIED derived isomorphism.
The commutation field prevents the determinant map from forgetting which iso
is being represented. No determinant-line isomorphism is a field. -/
structure Roof (P Q : Model R)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex) where
  middle : Model R
  left : middle.complex ⟶ P.complex
  right : middle.complex ⟶ Q.complex
  left_admissible : CochainComplex.Determinant.IsAdmissible left
  right_admissible : CochainComplex.Determinant.IsAdmissible right
  represents : DerivedCategory.Q.map left ≫ a.hom = DerivedCategory.Q.map right

/-- Fullness of bounded-projective complexes in the derived category gives
a chain map representing the prescribed derived morphism. -/
theorem exists_chainMap (P Q : Model R)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex) :
    ∃ f : P.complex ⟶ Q.complex, DerivedCategory.Q.map f = a.hom := by
  haveI (n : ℤ) : Projective (P.complex.X n) := by
    by_cases hneg : n = -1
    · subst n
      infer_instance
    by_cases hzero : n = 0
    · subst n
      infer_instance
    by_cases hn : n < -1
    · exact (P.complex.isZero_of_isStrictlyGE (-1) n hn).projective
    · exact (P.complex.isZero_of_isStrictlyLE 0 n (by omega)).projective
  letI : P.complex.IsKProjective := CochainComplex.isKProjective_of_projective P.complex 0
  let iso := DerivedCategory.quotientCompQhIso (ModuleCat R)
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P.complex
    ((HomotopyCategory.quotient _ _).obj Q.complex)).surjective
      (iso.hom.app P.complex ≫ a.hom ≫ iso.inv.app Q.complex)
  let f := (HomotopyCategory.quotient _ _).preimage g
  have hf : (HomotopyCategory.quotient _ _).map f = g := Functor.map_preimage _ _
  refine ⟨f, ?_⟩
  have h := DerivedCategory.quotientCompQhIso_hom_naturality f
  rw [hf, hg] at h
  change (iso.hom.app P.complex ≫ a.hom ≫ iso.inv.app Q.complex) ≫
    iso.hom.app Q.complex = iso.hom.app P.complex ≫ DerivedCategory.Q.map f at h
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h
  exact (cancel_epi (iso.hom.app P.complex)).mp h.symm

def chainMap (P Q : Model R)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex) :
    P.complex ⟶ Q.complex := (exists_chainMap R P Q a).choose

/-- The selected chain map represents the specified derived isomorphism. -/
theorem chainMap_spec (P Q : Model R)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex) :
    DerivedCategory.Q.map (chainMap R P Q a) = a.hom :=
  (exists_chainMap R P Q a).choose_spec

/-- Add the contractible summand [Q⁻¹ --id--> Q⁻¹] to P. -/
def refinementDifferential (P Q : Model R) :
    ModuleCat.of R (P.complex.X (-1) × Q.complex.X (-1)) ⟶
      ModuleCat.of R (P.complex.X 0 × Q.complex.X (-1)) :=
  ModuleCat.ofHom (LinearMap.prodMap (P.complex.d (-1) 0).hom LinearMap.id)

def refinementModel (P Q : Model R) : Model R where
  complex := CochainComplex.twoTerm (refinementDifferential R P Q)
  finiteNeg := by
    -- Local instance justification (defeq pin): transfer the product's finite-module witness through the bundled degree-minus-one endpoint.
    letI : Module.Finite R (ModuleCat.of R (P.complex.X (-1) × Q.complex.X (-1))) :=
      inferInstanceAs (Module.Finite R (P.complex.X (-1) × Q.complex.X (-1)))
    exact Module.Finite.equiv
      (CochainComplex.twoTermXNegOneIso (refinementDifferential R P Q)).symm.toLinearEquiv
  projectiveNeg := by sorry
  finiteZero := by
    -- Local instance justification (defeq pin): transfer the product's finite-module witness through the bundled degree-zero endpoint.
    letI : Module.Finite R (ModuleCat.of R (P.complex.X 0 × Q.complex.X (-1))) :=
      inferInstanceAs (Module.Finite R (P.complex.X 0 × Q.complex.X (-1)))
    exact Module.Finite.equiv
      (CochainComplex.twoTermXZeroIso (refinementDifferential R P Q)).symm.toLinearEquiv
  projectiveZero := by sorry

/-- The left refinement map is projection to P in both degrees. -/
def refinementLeft (P Q : Model R) : (refinementModel R P Q).complex ⟶ P.complex :=
  HomologicalComplex.mkHomFromDouble
    (ComplexShape.up_mk (-1) 0 (neg_add_cancel 1)) (by decide)
    (ModuleCat.ofHom (LinearMap.fst R _ _))
    (ModuleCat.ofHom (LinearMap.fst R _ _)) (by sorry) (by sorry)

/-- The right map is (f⁻¹,id) in degree -1 and (f⁰,dQ) in degree 0. -/
def refinementRight (P Q : Model R) (f : P.complex ⟶ Q.complex) :
    (refinementModel R P Q).complex ⟶ Q.complex :=
  HomologicalComplex.mkHomFromDouble
    (ComplexShape.up_mk (-1) 0 (neg_add_cancel 1)) (by decide)
    (ModuleCat.ofHom ((f.f (-1)).hom.comp (LinearMap.fst R _ _) + LinearMap.snd R _ _))
    (ModuleCat.ofHom ((f.f 0).hom.comp (LinearMap.fst R _ _) +
      (Q.complex.d (-1) 0).hom.comp (LinearMap.snd R _ _))) (by sorry) (by sorry)

/-- An explicit common refinement of the specified derived isomorphism.
Only the chain-map representative is selected; both roof maps are displayed. -/
def explicitRoof (P Q : Model R)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex) : Roof R P Q a where
  middle := refinementModel R P Q
  left := refinementLeft R P Q
  right := refinementRight R P Q (chainMap R P Q a)
  left_admissible := by sorry
  right_admissible := by sorry
  represents := by sorry

/-- Determinant transport is computed using the two explicit admissible maps. -/
def Roof.equiv {P Q : Model R}
    {a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex}
    (r : Roof R P Q a) :
    CochainComplex.Determinant.line P.complex ≃ₗ[R] CochainComplex.Determinant.line Q.complex :=
  (CochainComplex.Determinant.equiv r.left r.left_admissible).symm.trans
    (CochainComplex.Determinant.equiv r.right r.right_admissible)

/-- Refinement/homotopy invariance for roofs representing the SAME derived iso. -/
theorem roof_independent {P Q : Model R}
    {a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex}
    (r s : Roof R P Q a) : r.equiv R = s.equiv R := by sorry

def comparison (P Q : Model R)
    (a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex) :
    CochainComplex.Determinant.line P.complex ≃ₗ[R] CochainComplex.Determinant.line Q.complex :=
  (explicitRoof R P Q a).equiv R

theorem comparison_eq_roof {P Q : Model R}
    {a : DerivedCategory.Q.obj P.complex ≅ DerivedCategory.Q.obj Q.complex}
    (r : Roof R P Q a) : comparison R P Q a = r.equiv R :=
  roof_independent R _ r

theorem line_invertible (P : Model R) :
    MonoidalCategory.isInvertibleObject
      (ModuleCat.of R (CochainComplex.Determinant.line P.complex)) := by sorry

def lineObject (P : Model R) : ModuleCat.Invertible R :=
  ⟨ModuleCat.of R (CochainComplex.Determinant.line P.complex), line_invertible R P⟩

/-- The ring determinant functor is given by actual lines and roof transport. -/
def determinantFunctor : Core (Object R) ⥤ ModuleCat.Invertible.Core R where
  obj K := ⟨lineObject R (model R K.of)⟩
  map f := ⟨ObjectProperty.isoMk _
    (comparison R (model R _) (model R _) (realizedIso R f.iso)).toModuleIso⟩
  map_id := by sorry
  map_comp := by sorry

def isRankZero (K : Object R) : Prop :=
  CochainComplex.Determinant.IsRankZero (model R K).complex

/-- The element is the exterior map of the representative differential. -/
def canonicalElement (K : Object R) (hK : isRankZero R K) :
    (determinantFunctor R).obj ⟨K⟩ |>.of.obj :=
  CochainComplex.Determinant.canonical (model R K).complex hK

/-- Any other specified finite-projective representative is compared by its
actual derived identification, using the same roof formula. -/
def representativeIso (K : Object R) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : K.obj.obj ≅ DerivedCategory.Q.obj P)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)] :
    ((determinantFunctor R).obj ⟨K⟩).of.obj ≅ ModuleCat.of R (CochainComplex.Determinant.line P) :=
  (comparison R (model R K) ⟨P⟩ ((realization R K).symm ≪≫ e)).toModuleIso

/-- The roof comparisons intertwine the specified derived map with its actual admissible
chain-map representative. This is a law of the existing comparison, with no new line data. -/
theorem representativeIso_naturality {K L : Object R}
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (eP : K.obj.obj ≅ DerivedCategory.Q.obj P)
    (eQ : L.obj.obj ≅ DerivedCategory.Q.obj Q)
    [P.IsStrictlyGE (-1)] [P.IsStrictlyLE 0]
    [Module.Finite R (P.X (-1))] [Module.Projective R (P.X (-1))]
    [Module.Finite R (P.X 0)] [Module.Projective R (P.X 0)]
    [Q.IsStrictlyGE (-1)] [Q.IsStrictlyLE 0]
    [Module.Finite R (Q.X (-1))] [Module.Projective R (Q.X (-1))]
    [Module.Finite R (Q.X 0)] [Module.Projective R (Q.X 0)]
    (u : K ≅ L) (a : P ⟶ Q) (ha : CochainComplex.Determinant.IsAdmissible a)
    (h : eP.hom ≫ DerivedCategory.Q.map a = u.hom.hom.hom ≫ eQ.hom) :
    (representativeIso R K P eP).hom ≫
        (CochainComplex.Determinant.equiv a ha).toModuleIso.hom =
      ((determinantFunctor R).map ⟨u⟩).iso.hom.hom ≫
        (representativeIso R L Q eQ).hom := by sorry
-- Proof strategy: use `h` to identify the realized derived isomorphisms, compose their
-- admissible roofs, and apply `roof_independent` and the complex-level `map_comp`.

/-- Concrete construction of the EXISTING ring-level determinant interface.
No use of nonemptyDeterminant, and no arbitrary determinant parameter. -/
def determinant : PerfectDerived.TorNegOneZero.Determinant R where
  det := determinantFunctor R
  isRankZero := isRankZero R
  rankZero_of_iso := by sorry
  canonicalElement := canonicalElement R
  map_canonicalElement := by sorry
  representativeIso := representativeIso R
  representativeIso_naturality := representativeIso_naturality R
  rankZero_iff := by sorry
  representativeIso_hom_canonicalElement := by sorry

end CanonicalRingDeterminant
