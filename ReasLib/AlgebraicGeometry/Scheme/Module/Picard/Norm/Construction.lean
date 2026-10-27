/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.FiniteLocallyFree
public import ReasLib.RingTheory.Norm.PolynomialLaw
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.FiniteEvaluation
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Finite locally free norms on sections

On a finite local basis, the norm is the determinant of multiplication. Restriction
preserves the chosen basis vectors, hence the local norm values agree on overlaps.
The native structure-sheaf descent equivalence assembles these explicit local values
into the norm section; its invertibility certificate depends only on the structure sheaf.
The file also specializes the finite-projective algebra norm and its polynomial law to
section algebras with explicit finite-generation and projectivity inputs.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace Opposite
open scoped TensorProduct

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (π : X ⟶ Y)

-- Use the native small-site slice instances; the larger-universe bridge instances are not
-- needed for the equal-universe structure module and currently have unproved certificates.
attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver in
/-- The defining local-generator witness gives local freeness of the pushforward directly. -/
theorem finiteLocallyFree_pushforward_isLocallyFree [h : IsFiniteLocallyFree π] :
    π.pushforwardStructureModule.IsLocallyFree := by
  obtain ⟨q, hq, _⟩ := h.pushforward_isFiniteLocallyFree.exists_data
  exact ⟨q, hq⟩

attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver in
/-- The same defining witness gives finite type without using a finite-local-freeness bridge. -/
theorem finiteLocallyFree_pushforward_isFiniteType [h : IsFiniteLocallyFree π] :
    π.pushforwardStructureModule.IsFiniteType := by
  obtain ⟨q, _, hq⟩ := h.pushforward_isFiniteLocallyFree.exists_data
  exact ⟨q, hq⟩

attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver in
/-- The native locally free presentation has no relations, hence is quasi-coherent. -/
theorem finiteLocallyFree_pushforward_isQuasicoherent [h : IsFiniteLocallyFree π] :
    π.pushforwardStructureModule.IsQuasicoherent := by
  obtain ⟨q, hq, _⟩ := h.pushforward_isFiniteLocallyFree.exists_data
  letI := hq
  exact q.quasiCoherentData.isQuasicoherent

attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver in
/-- Finite local bases give a finite presentation, using the native presentation with no
relations. This proves the sheaf-level step without the admitted affine-section criterion. -/
theorem finiteLocallyFree_pushforward_isFinitePresentation [h : IsFiniteLocallyFree π] :
    π.pushforwardStructureModule.IsFinitePresentation := by
  letI : ∀ U : Y.Opens,
      HasWeakSheafify ((Opens.grothendieckTopology Y).over U)
        AddCommGrpCat.{u} := fun U ↦ inferInstance
  letI : ∀ U : Y.Opens,
      ((Opens.grothendieckTopology Y).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} := fun U ↦ inferInstance
  obtain ⟨q, hq, hfinite⟩ := h.pushforward_isFiniteLocallyFree.exists_data
  letI := hq
  letI := hfinite
  refine ⟨q.quasiCoherentData, ⟨fun i ↦ ⟨hfinite.isFiniteType i, ⟨?_⟩⟩⟩⟩
  exact (inferInstance : Finite (ULift.{u} Empty))

namespace FiniteLocallyFreeNormConstruction

set_option backward.isDefEq.respectTransparency false in
open SheafOfModules in
private theorem freeEvaluationIso_freeSection
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (I : Type u) [Finite I] (U : Cᵒᵖ) (i : I) :
    (freeEvaluationIso R I U).hom ((freeSection (R := R) i).val U) =
      Pi.basisFun (R.obj.obj U) I i := by
  classical
  letI : CategoryTheory.Limits.HasFiniteBiproducts (SheafOfModules.{u} R) :=
    CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
  have h (j : I) :
      ιFree (R := R) i ≫ (CategoryTheory.Limits.biproductIso (fun _ : I ↦ unit R)).inv ≫
          CategoryTheory.Limits.Pi.π (fun _ : I ↦ unit R) j =
        if h : i = j then eqToHom (congrArg (fun _ : I ↦ unit R) h) else 0 := by
    change CategoryTheory.Limits.Sigma.ι (fun _ : I ↦ unit R) i ≫
        (CategoryTheory.Limits.biproduct.isoCoproduct (fun _ : I ↦ unit R)).inv ≫
        (CategoryTheory.Limits.biproduct.isoProduct (fun _ : I ↦ unit R)).hom ≫
        CategoryTheory.Limits.Pi.π (fun _ : I ↦ unit R) j = _
    rw [CategoryTheory.Limits.biproduct.isoCoproduct_inv,
      CategoryTheory.Limits.biproduct.isoProduct_hom, ← Category.assoc, ← Category.assoc,
      CategoryTheory.Limits.Sigma.ι_desc, Category.assoc, CategoryTheory.Limits.Pi.lift_π,
      CategoryTheory.Limits.biproduct.ι_π]
  have hc (j : I) :
      (SheafOfModules.evaluation R U).map (ιFree (R := R) i) ≫ (freeEvaluationIso R I U).hom ≫
          ModuleCat.ofHom (LinearMap.proj j) =
        (SheafOfModules.evaluation R U).map
          (if h : i = j then eqToHom (congrArg (fun _ : I ↦ unit R) h) else 0) := by
    simp only [freeEvaluationIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype,
      CategoryTheory.Limits.PreservesProduct.iso_hom, CategoryTheory.Limits.piComparison_comp_π]
    simpa only [Functor.map_comp, Category.assoc] using congrArg ((SheafOfModules.evaluation R U).map) (h j)
  ext j
  have hj := congrArg (fun f ↦ f (1 : R.obj.obj U)) (hc j)
  by_cases hij : i = j
  · subst j
    convert hj using 1 <;>
      simp [freeSection, freeHomEquiv, Pi.basisFun_apply, SheafOfModules.evaluation] <;> rfl
  · convert hj using 1 <;>
      simp [freeSection, freeHomEquiv, Pi.basisFun_apply, SheafOfModules.evaluation,
        hij, Ne.symm hij] <;> rfl

open SheafOfModules in
private theorem evaluated_generatingSections_basis_apply
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {M : SheafOfModules.{u} R}
    (s : M.GeneratingSections) [s.IsFiniteType] [IsIso s.π] (U : Cᵒᵖ) (i : s.I) :
    s.basis U i = (s.s i).val U := by
  classical
  rw [GeneratingSections.basis, Module.Basis.map_apply,
    ← freeEvaluationIso_freeSection R s.I U i]
  change s.π.val.app U
      ((freeEvaluationIso R s.I U).inv
        ((freeEvaluationIso R s.I U).hom ((freeSection (R := R) i).val U))) = _
  rw [← ModuleCat.comp_apply, Iso.hom_inv_id]
  exact congrArg (fun t ↦ t.val U)
    (sectionsMap_freeHomEquiv_symm_freeSection s.s i)

private theorem map_generatingSections_basis
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {M : SheafOfModules.{u} R}
    (s : M.GeneratingSections) [s.IsFiniteType] [IsIso s.π]
    {V W : Cᵒᵖ} (h : V ⟶ W) (j : s.I) :
    M.val.map h (s.basis V j) = s.basis W j := by
  rw [evaluated_generatingSections_basis_apply, evaluated_generatingSections_basis_apply]
  exact PresheafOfModules.sections_property (s.s j) h

private theorem norm_map_of_basis {R S A B : Type*} [CommRing R] [CommRing S]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
    {I : Type*} [Finite I]
    (b : Module.Basis I R A) (c : Module.Basis I S B)
    (r : R →+* S) (a : A →+* B)
    (ha : ∀ t x, a (t • x) = r t • a x) (hb : ∀ i, a (b i) = c i) (x : A) :
    r (Algebra.norm R x) = Algebra.norm S (a x) := by
  classical
  letI := Fintype.ofFinite I
  have hre (y : A) (i : I) : c.repr (a y) i = r (b.repr y i) := by
    have hy : a y = ∑ j, r (b.repr y j) • c j := by
      conv_lhs => rw [← b.sum_repr y]
      simp only [map_sum, ha, hb]
    rw [hy]
    exact congrFun (c.repr_sum_self (fun j ↦ r (b.repr y j))) i
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det c, r.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    ← hb, ← map_mul, hre]

attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver in
/-- Choose local finite bases only from the defining, caller-supplied local-freeness witness. -/
def cover [h : IsFiniteLocallyFree π] : π.pushforwardStructureModule.LocalGeneratorsData :=
  h.pushforward_isFiniteLocallyFree.exists_data.choose

attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver in
/-- The chosen local generators are bases, by the original witness. -/
theorem cover_isLocallyFree [h : IsFiniteLocallyFree π] : (cover π).IsLocallyFreeData :=
  h.pushforward_isFiniteLocallyFree.exists_data.choose_spec.1

attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver in
/-- The chosen local basis indexing types are finite, by the original witness. -/
theorem cover_isFiniteType [h : IsFiniteLocallyFree π] : (cover π).IsFiniteType :=
  h.pushforward_isFiniteLocallyFree.exists_data.choose_spec.2

/-- Intersect the trivializing cover with the open on which the norm is to be evaluated. -/
def opens [IsFiniteLocallyFree π] (U : Y.Opens) (i : (cover π).I) : Y.Opens :=
  U ⊓ (cover π).X i

/-- These intersections cover the specified open. -/
theorem iSup_opens [IsFiniteLocallyFree π] (U : Y.Opens) :
    (⨆ i, opens π U i) = U := by
  have hc : (⨆ i, (cover π).X i) = ⊤ := by
    simpa only [Opens.coversTop_iff, IsOpenCover] using (cover π).coversTop
  simp only [opens, ← inf_iSup_eq, hc, inf_top_eq]

/-- The native sheaf equivalence between sections and compatible families on the chosen
cover. Its invertibility certificate depends only on the structure sheaf, independently
of any family of local norm values supplied later. -/
def sectionsEquiv [IsFiniteLocallyFree π] (U : Y.Opens) :
    Γ(Y, ⨆ i, opens π U i) ≃
      (((Pairwise.diagram (opens π U)).op ⋙
        (Y.presheaf ⋙ CategoryTheory.forget CommRingCat)).sections) := by
  have h : TopCat.Presheaf.IsSheaf (Y.presheaf ⋙ CategoryTheory.forget CommRingCat) :=
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (CategoryTheory.forget CommRingCat) Y.presheaf).mp Y.sheaf.2
  exact CategoryTheory.Limits.Types.isLimitEquivSections
    (h.isSheafPairwiseIntersections (opens π U)).some

attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver in
/-- The actual finite basis of a section algebra on a member of the trivializing cover. -/
def localBasis [IsFiniteLocallyFree π] (U : Y.Opens) (i : (cover π).I) :
    Module.Basis ((cover π).generators i).I (Γ(Y, opens π U i))
      (Γ(X, π ⁻¹ᵁ opens π U i)) := by
  letI := cover_isLocallyFree π
  letI := (cover_isFiniteType π).isFiniteType i
  exact ((cover π).generators i).basis (op (Over.mk (homOfLE (show
    opens π U i ≤ (cover π).X i from inf_le_right))))

attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver in
/-- Evaluate the finite-free algebra norm on a member of the trivializing cover. -/
def localApp [IsFiniteLocallyFree π] (U : Y.Opens) (i : (cover π).I) :
    Γ(X, π ⁻¹ᵁ opens π U i) →* Γ(Y, opens π U i) := by
  letI := cover_isLocallyFree π
  letI := (cover_isFiniteType π).isFiniteType i
  let b := localBasis π U i
  letI : Module.Free (Γ(Y, opens π U i)) (Γ(X, π ⁻¹ᵁ opens π U i)) :=
    Module.Free.of_basis b
  letI : Module.Finite (Γ(Y, opens π U i)) (Γ(X, π ⁻¹ᵁ opens π U i)) :=
    Module.Finite.of_basis b
  exact Algebra.norm (Γ(Y, opens π U i))

/-- The local norm is the determinant of multiplication in the displayed local finite basis. -/
theorem localApp_eq_det [IsFiniteLocallyFree π] (U : Y.Opens) (i : (cover π).I)
    (b : Γ(X, π ⁻¹ᵁ opens π U i)) :
    letI := (cover_isFiniteType π).isFiniteType i
    letI := Fintype.ofFinite ((cover π).generators i).I
    letI := Classical.decEq ((cover π).generators i).I
    localApp π U i b = Matrix.det (Algebra.leftMulMatrix (localBasis π U i) b) := by
  letI := (cover_isFiniteType π).isFiniteType i
  letI := Fintype.ofFinite ((cover π).generators i).I
  classical
  exact Algebra.norm_eq_matrix_det (localBasis π U i) b

/-- The local values used for descent are explicit restrictions followed by finite-free norms. -/
def localValues [IsFiniteLocallyFree π] (U : Y.Opens) (b : Γ(X, π ⁻¹ᵁ U))
    (i : (cover π).I) : Γ(Y, opens π U i) :=
  localApp π U i (X.presheaf.map (homOfLE (π.preimage_mono inf_le_left)).op b)

attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver in
/-- Evaluate one of the original local bases on any smaller open. -/
def chartBasis [IsFiniteLocallyFree π] (i : (cover π).I) (V : Y.Opens)
    (hV : V ≤ (cover π).X i) :
    Module.Basis ((cover π).generators i).I (Γ(Y, V)) (Γ(X, π ⁻¹ᵁ V)) := by
  letI := cover_isLocallyFree π
  letI := (cover_isFiniteType π).isFiniteType i
  exact ((cover π).generators i).basis (op (Over.mk (homOfLE hV)))

attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver in
set_option backward.isDefEq.respectTransparency false in
/-- The original local basis is preserved by restriction inside its chart. -/
theorem chartBasis_restrict [IsFiniteLocallyFree π] (i : (cover π).I)
    (V W : Y.Opens) (hV : V ≤ (cover π).X i) (hW : W ≤ (cover π).X i)
    (h : W ≤ V) (j : ((cover π).generators i).I) :
    X.presheaf.map (homOfLE (π.preimage_mono h)).op (chartBasis π i V hV j) =
      chartBasis π i W hW j := by
  letI := cover_isLocallyFree π
  letI := (cover_isFiniteType π).isFiniteType i
  let a : Over.mk (homOfLE hW) ⟶ Over.mk (homOfLE hV) := Over.homMk (homOfLE h)
  exact map_generatingSections_basis ((cover π).generators i) a.op j

attribute [-instance] TopCat.addCommGrpHasWeakSheafifyOver
  TopCat.addCommGrpWEqualsLocallyBijectiveOver in
set_option backward.isDefEq.respectTransparency false in
/-- Coordinates in one of the local bases restrict along the structure-sheaf ring map. -/
theorem chartBasis_repr_restrict [IsFiniteLocallyFree π] (i : (cover π).I)
    (V W : Y.Opens) (hV : V ≤ (cover π).X i) (hW : W ≤ (cover π).X i)
    (h : W ≤ V) (x : Γ(X, π ⁻¹ᵁ V)) (j : ((cover π).generators i).I) :
    (chartBasis π i W hW).repr
        (X.presheaf.map (homOfLE (π.preimage_mono h)).op x) j =
      Y.presheaf.map (homOfLE h).op ((chartBasis π i V hV).repr x j) := by
  classical
  letI := (cover_isFiniteType π).isFiniteType i
  letI := Fintype.ofFinite ((cover π).generators i).I
  have hsmul (t : Γ(Y, V)) (y : Γ(X, π ⁻¹ᵁ V)) :
      X.presheaf.map (homOfLE (π.preimage_mono h)).op (t • y) =
        Y.presheaf.map (homOfLE h).op t •
          X.presheaf.map (homOfLE (π.preimage_mono h)).op y :=
    π.pushforwardStructureModule.val.map_smul (homOfLE h).op t y
  conv_lhs => rw [← (chartBasis π i V hV).sum_repr x]
  simp only [map_sum, hsmul, chartBasis_restrict π i V W hV hW h]
  simpa only [map_sum] using congrFun ((chartBasis π i W hW).repr_sum_self
    (fun k ↦ Y.presheaf.map (homOfLE h).op ((chartBasis π i V hV).repr x k))) j

set_option backward.isDefEq.respectTransparency false in
/-- Norms computed in an original local basis commute with restriction inside its chart. -/
theorem chartNorm_restrict [IsFiniteLocallyFree π] (i : (cover π).I)
    (V W : Y.Opens) (hV : V ≤ (cover π).X i) (hW : W ≤ (cover π).X i)
    (h : W ≤ V) (x : Γ(X, π ⁻¹ᵁ V)) :
    Y.presheaf.map (homOfLE h).op (Algebra.norm (Γ(Y, V)) x) =
      Algebra.norm (Γ(Y, W)) (X.presheaf.map (homOfLE (π.preimage_mono h)).op x) := by
  classical
  letI := (cover_isFiniteType π).isFiniteType i
  letI := Fintype.ofFinite ((cover π).generators i).I
  refine norm_map_of_basis (chartBasis π i V hV) (chartBasis π i W hW)
    (Y.presheaf.map (homOfLE h).op).hom
    (X.presheaf.map (homOfLE (π.preimage_mono h)).op).hom ?_
    (chartBasis_restrict π i V W hV hW h) x
  intro t y
  exact π.pushforwardStructureModule.val.map_smul (homOfLE h).op t y

set_option backward.isDefEq.respectTransparency false in
/-- Local determinant formulas commute with restriction and changes of finite local basis. -/
theorem localValues_compatible [IsFiniteLocallyFree π] (U : Y.Opens)
    (b : Γ(X, π ⁻¹ᵁ U)) :
    TopCat.Presheaf.IsCompatible (Y.presheaf ⋙ CategoryTheory.forget CommRingCat)
      (opens π U) (localValues π U b) := by
  intro i j
  change Y.presheaf.map (homOfLE inf_le_left).op (localValues π U b i) =
    Y.presheaf.map (homOfLE inf_le_right).op (localValues π U b j)
  unfold localValues
  change Y.presheaf.map (homOfLE inf_le_left).op (Algebra.norm _ _) =
    Y.presheaf.map (homOfLE inf_le_right).op (Algebra.norm _ _)
  rw [chartNorm_restrict π i (opens π U i) (opens π U i ⊓ opens π U j) inf_le_right
      (inf_le_left.trans inf_le_right) inf_le_left,
    chartNorm_restrict π j (opens π U j) (opens π U i ⊓ opens π U j) inf_le_right
      (inf_le_right.trans inf_le_right) inf_le_right]
  apply congrArg (Algebra.norm (Γ(Y, opens π U i ⊓ opens π U j)))
  let ai : op (π ⁻¹ᵁ U) ⟶ op (π ⁻¹ᵁ opens π U i) :=
    (homOfLE (π.preimage_mono inf_le_left)).op
  let aj : op (π ⁻¹ᵁ U) ⟶ op (π ⁻¹ᵁ opens π U j) :=
    (homOfLE (π.preimage_mono inf_le_left)).op
  let bi : op (π ⁻¹ᵁ opens π U i) ⟶ op (π ⁻¹ᵁ (opens π U i ⊓ opens π U j)) :=
    (homOfLE (π.preimage_mono inf_le_left)).op
  let bj : op (π ⁻¹ᵁ opens π U j) ⟶ op (π ⁻¹ᵁ (opens π U i ⊓ opens π U j)) :=
    (homOfLE (π.preimage_mono inf_le_right)).op
  have hmap : X.presheaf.map ai ≫ X.presheaf.map bi =
      X.presheaf.map aj ≫ X.presheaf.map bj := by
    rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    rfl
  exact ConcreteCategory.congr_hom hmap b

/-- The native compatible-family object has the explicit local values as its data.
Compatibility is an equation law; no existence or invertibility certificate is extracted
from it. -/
def familyOfCompatible [IsFiniteLocallyFree π] (U : Y.Opens) (b : Γ(X, π ⁻¹ᵁ U))
    (hcompat : TopCat.Presheaf.IsCompatible (Y.presheaf ⋙ CategoryTheory.forget CommRingCat)
      (opens π U) (localValues π U b)) :
    (((Pairwise.diagram (opens π U)).op ⋙
      (Y.presheaf ⋙ CategoryTheory.forget CommRingCat)).sections) :=
  hcompat.sectionPairwise

end FiniteLocallyFreeNormConstruction

/-- The finite locally free norm on arbitrary opens, evaluated by the native structure-sheaf
descent equivalence on explicit local determinant values. The inverse equivalence is proved
before and independently of the input compatible family. -/
def finiteLocallyFreeNormAppOfCompatible [IsFiniteLocallyFree π] (U : Y.Opens)
    (b : Γ(X, π ⁻¹ᵁ U))
    (hcompat : TopCat.Presheaf.IsCompatible (Y.presheaf ⋙ CategoryTheory.forget CommRingCat)
      (FiniteLocallyFreeNormConstruction.opens π U)
      (FiniteLocallyFreeNormConstruction.localValues π U b)) : Γ(Y, U) :=
  Y.presheaf.map (eqToHom (FiniteLocallyFreeNormConstruction.iSup_opens π U).symm).op
    ((FiniteLocallyFreeNormConstruction.sectionsEquiv π U).symm
      (FiniteLocallyFreeNormConstruction.familyOfCompatible π U b hcompat))

/-- The global norm has the prescribed local determinant values. -/
theorem finiteLocallyFreeNormAppOfCompatible_restrict [IsFiniteLocallyFree π] (U : Y.Opens)
    (b : Γ(X, π ⁻¹ᵁ U))
    (hcompat : TopCat.Presheaf.IsCompatible (Y.presheaf ⋙ CategoryTheory.forget CommRingCat)
      (FiniteLocallyFreeNormConstruction.opens π U)
      (FiniteLocallyFreeNormConstruction.localValues π U b))
    (i : (FiniteLocallyFreeNormConstruction.cover π).I) :
    Y.presheaf.map (homOfLE (show
        FiniteLocallyFreeNormConstruction.opens π U i ≤ U from inf_le_left)).op
        (finiteLocallyFreeNormAppOfCompatible π U b hcompat) =
      FiniteLocallyFreeNormConstruction.localValues π U b i := by
  let c := FiniteLocallyFreeNormConstruction.opens π U
  let z := FiniteLocallyFreeNormConstruction.familyOfCompatible π U b hcompat
  have hz := congrArg (fun s ↦ s.val (op (Pairwise.single i)))
    ((FiniteLocallyFreeNormConstruction.sectionsEquiv π U).apply_symm_apply z)
  change Y.presheaf.map (homOfLE (le_iSup c i)).op
      ((FiniteLocallyFreeNormConstruction.sectionsEquiv π U).symm z) =
    FiniteLocallyFreeNormConstruction.localValues π U b i at hz
  unfold finiteLocallyFreeNormAppOfCompatible
  rw [← CommRingCat.comp_apply, ← Y.presheaf.map_comp]
  exact hz

/-- The finite locally free norm on sections of an arbitrary open. The local determinant
values are glued using their proved compatibility and the native structure sheaf. -/
def finiteLocallyFreeNormApp [IsFiniteLocallyFree π] (U : Y.Opens)
    (b : Γ(X, π ⁻¹ᵁ U)) : Γ(Y, U) :=
  finiteLocallyFreeNormAppOfCompatible π U b
    (FiniteLocallyFreeNormConstruction.localValues_compatible π U b)

/-- On each trivializing open the constructed norm is the finite-free algebra norm. -/
theorem finiteLocallyFreeNormApp_restrict [IsFiniteLocallyFree π] (U : Y.Opens)
    (b : Γ(X, π ⁻¹ᵁ U)) (i : (FiniteLocallyFreeNormConstruction.cover π).I) :
    Y.presheaf.map (homOfLE (show
        FiniteLocallyFreeNormConstruction.opens π U i ≤ U from inf_le_left)).op
        (finiteLocallyFreeNormApp π U b) =
      FiniteLocallyFreeNormConstruction.localValues π U b i :=
  finiteLocallyFreeNormAppOfCompatible_restrict π U b _ i

variable (U : Y.Opens)
  [Module.Finite (Γ(Y, U)) (Γ(X, π ⁻¹ᵁ U))]
  [Module.Projective (Γ(Y, U)) (Γ(X, π ⁻¹ᵁ U))]

/-- The section-algebra norm, computed by the canonical finite-projective determinant. -/
def finiteProjectiveSectionNorm : Γ(X, π ⁻¹ᵁ U) → Γ(Y, U) :=
  Algebra.finiteProjectiveNorm (Γ(Y, U))

/-- The section norm has the explicit determinant-of-multiplication formula. -/
theorem finiteProjectiveSectionNorm_apply (b : Γ(X, π ⁻¹ᵁ U)) :
    finiteProjectiveSectionNorm π U b =
      LinearMap.projectiveDet (Algebra.lmul (Γ(Y, U)) (Γ(X, π ⁻¹ᵁ U)) b) := rfl

/-- The multiplicative section norm uses the same underlying function. -/
def finiteProjectiveSectionNormHom : Γ(X, π ⁻¹ᵁ U) →* Γ(Y, U) :=
  Algebra.finiteProjectiveNormHom (Γ(Y, U))

/-- The multiplicative packaging does not change the section norm's data. -/
theorem finiteProjectiveSectionNormHom_toFun :
    (finiteProjectiveSectionNormHom π U).toFun = finiteProjectiveSectionNorm π U := rfl

/-- The polynomial law of the section-algebra norm is the canonical algebra norm law. -/
def finiteProjectiveSectionNormPolynomialLaw :
    Γ(X, π ⁻¹ᵁ U) →ₚₗ[Γ(Y, U)] Γ(Y, U) :=
  Algebra.finiteProjectiveNormPolynomialLaw (Γ(Y, U)) (Γ(X, π ⁻¹ᵁ U))

/-- After scalar extension, evaluate the determinant of multiplication in the extended algebra.
The module-finiteness and projectivity instances here are the proved tensor-product instances.
-/
def finiteProjectiveSectionNormBaseChange (A : Type v) [CommRing A] [Algebra (Γ(Y, U)) A] :
    (A ⊗[Γ(Y, U)] Γ(X, π ⁻¹ᵁ U)) → A :=
  Algebra.finiteProjectiveNorm A

/-- The polynomial law agrees with the explicit norm formula after extension of scalars. -/
theorem finiteProjectiveSectionNormPolynomialLaw_toFun
    (A : Type v) [CommRing A] [Algebra (Γ(Y, U)) A]
    (b : A ⊗[Γ(Y, U)] Γ(X, π ⁻¹ᵁ U)) :
    Algebra.TensorProduct.rid (Γ(Y, U)) A A
        ((finiteProjectiveSectionNormPolynomialLaw π U).toFun A b) =
      finiteProjectiveSectionNormBaseChange π U A b :=
  Algebra.finiteProjectiveNormPolynomialLaw_toFun (Γ(Y, U)) (Γ(X, π ⁻¹ᵁ U)) A b

end AlgebraicGeometry.Scheme
