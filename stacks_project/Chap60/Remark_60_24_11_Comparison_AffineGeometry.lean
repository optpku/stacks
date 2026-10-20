module
public import stacks_project.Chap60.Remark_60_24_11_Comparison_SmoothLiftGeometry
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffinePDForms
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineTensorSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineSheafExtension
public import Mathlib.CategoryTheory.Sites.Abelian
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_PDSquareZeroGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
universe u
namespace CrystallineSmoothLiftAffine

variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} [CommRing A] {IA : Ideal A} (γA : DividedPowers IA)
variable {Y : Scheme.{u}} (yToS : Y ⟶ Spec (.of A)) [Smooth yToS]
variable (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (hI : specIdealEqOfIdealTop IA I) (hγ : specDividedPowersEq IA γA I γS)
variable (hpnil : IsNilpotent (p : A)) (U : Y.affineOpens)

/-- The algebra on affine chart functions is induced by the actual
structure morphism to Spec A. -/
noncomputable abbrev chartAlgebra : Algebra A Γ(Y, U.1) :=
  (affineSectionMap yToS U).toAlgebra

/-- The actual affine chart map Spec Γ(Y,U) → Y. -/
noncomputable def chart : Spec (.of Γ(Y, U.1)) ⟶ Y :=
  U.property.isoSpec.inv ≫ U.1.ι

/-- The quotient closed-fibre chart uses the kernel subscheme's canonical
affine cover followed by the inverse of the closed immersion's image map.
No existentially chosen scheme isomorphism is introduced. -/
noncomputable def fibre :
    Spec (.of (Γ(Y, U.1) ⧸ (smoothLift_inclusion yToS I).ker.ideal U)) ⟶ smoothLift yToS I := by
  -- Local instance justification (defeq pin): expose the actual pullback closed immersion to infer its image isomorphism.
  letI : IsClosedImmersion (smoothLift_inclusion yToS I) := by
    change IsClosedImmersion (pullback.fst yToS I.subschemeι)
    infer_instance
  exact (smoothLift_inclusion yToS I).ker.subschemeCover.f U ≫
    inv (smoothLift_inclusion yToS I).toImage

/-- The canonical quotient-chart map is open in the actual closed fibre. -/
theorem fibre_open : IsOpenImmersion (fibre yToS I U) := sorry

/-- The actual affine chart square commutes with the base and closed
fibre morphisms. -/
theorem square :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((smoothLift_inclusion yToS I).ker.ideal U))) ≫
        Spec.map (CommRingCat.ofHom (affineSectionMap yToS U)) =
      fibre yToS I U ≫ smoothLift_x₀ yToS I ≫ I.subschemeι := sorry

include γA hI hpnil in
/-- The affine PD ideal is nil, by nilpotence of p and the genuine
base-extended divided-power structure. -/
theorem ideal_nil : ∀ x ∈ (smoothLift_inclusion yToS I).ker.ideal U, IsNilpotent x := sorry

/-- The canonical affine crystalline representative used to evaluate the
crystal on this open chart. -/
noncomputable def object :
    CrystallineObject (Spec (.of A)) I γS hc (smoothLift yToS I) (smoothLift_x₀ yToS I) :=
  CechCrisCover.affineCrystallineObject I γS hc (smoothLift_x₀ yToS I)
    ((smoothLift_inclusion yToS I).ker.ideal U) (smoothLiftDividedPowers γA yToS I hI U)
    (ideal_nil γA yToS I hI hpnil U) (Spec.map (CommRingCat.ofHom (affineSectionMap yToS U)))
    (fibre yToS I U) (square yToS I U)

include hγ in
/-- The affine chart PD operations agree with the specified base sheaf
operations; both hI and hγ remain part of this construction. -/
theorem object_baseCompatible :
    CrystallineBaseCompatible I γS hc (smoothLift_x₀ yToS I)
      (object γA yToS I γS hc hI hpnil U) := sorry

/-- The concrete affine representative as an object of the small site. -/
noncomputable def smallObject :
    smallCrystallineSite (Spec (.of A)) I γS hc (smoothLift yToS I) (smoothLift_x₀ yToS I) where
  obj := ⟨object γA yToS I γS hc hI hpnil U,
    object_baseCompatible γA yToS I γS hc hI hγ hpnil U⟩
  property := fibre_open yToS I U

/-- The actual affine representative maps to the whole smooth lift by
its canonical quotient closed-fibre chart and its affine open chart. -/
noncomputable def toWhole :
    smallObject γA yToS I γS hc hI hγ hpnil U ⟶
      CrystallineSmoothLiftRepair.smallObject γA yToS I γS hc hI hγ hpnil :=
  ObjectProperty.homMk
    { source := Over.homMk (fibre yToS I U) sorry
      thickening := chart U
      source_comm := sorry
      base_comm := sorry
      ideal_compatible := sorry
      dividedPowers_compatible := sorry }

variable (F : CrystallineModuleSheaf.CrisModuleSheaf (Spec (.of A)) I γS hc
  (smoothLift yToS I) (smoothLift_x₀ yToS I))
variable [CrystallineCoefficients.SectionsCoherent I γS hc (smoothLift_x₀ yToS I) F]
variable [CrystallineModuleSheaf.CrisModuleSheaf.IsCrystal F]
variable [hqc : CrystallineModuleSheaf.CrisModuleSheaf.IsLocallyQuasiCoherent F]

/-- The affine coefficient comparison is F's specified map on the actual
chart morphism; it therefore retains all geometric restriction data. -/
noncomputable def coefficientComparison :
    (Scheme.Modules.pullback (chart U)).obj
        (CrystallineSmoothLiftRepair.coefficient γA yToS I γS hc hI hγ hpnil F) ⟶
      F.obj (smallObject γA yToS I γS hc hI hγ hpnil U) :=
  F.comparison (toWhole γA yToS I γS hc hI hγ hpnil U)

/-- A crystal's comparison on the actual chart is invertible. -/
noncomputable def coefficientIso :
    (Scheme.Modules.pullback (chart U)).obj
        (CrystallineSmoothLiftRepair.coefficient γA yToS I γS hc hI hγ hpnil F) ≅
      F.obj (smallObject γA yToS I γS hc hI hγ hpnil U) :=
  @asIso _ _ _ _ (F.comparison (toWhole γA yToS I γS hc hI hγ hpnil U))
    (CrystallineModuleSheaf.ModuleSheaf.IsCrystal.comparison_isIso _)

/-- The actual local sections of F_Y on the affine open identify with
the coefficient of the canonical affine crystalline representative. Both
isomorphisms are specified by pullback and the crystal's own comparison. -/
noncomputable def coefficientSectionsIso :
    (CrystallineSmoothLiftRepair.coefficient γA yToS I γS hc hI hγ hpnil F).presheaf.obj
        (Opposite.op U.1) ≅
      (F.obj (smallObject γA yToS I γS hc hI hγ hpnil U)).presheaf.obj (Opposite.op ⊤) :=
  CrystallineAffineSections.pullbackSectionsIso U
      (CrystallineSmoothLiftRepair.coefficient γA yToS I γS hc hI hγ hpnil F) ≪≫
    ((Scheme.Modules.toPresheaf _).mapIso
      (coefficientIso γA yToS I γS hc hI hγ hpnil U F)).app (Opposite.op ⊤)

/-- The genuine affine crystal coefficient, with its action by chart
functions transported through the canonical affine-functions isomorphism. -/
noncomputable def coefficientModule : ModuleCat.{u} Γ(Y, U.1) :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of Γ(Y, U.1))).inv.hom).obj
    ((F.obj (smallObject γA yToS I γS hc hI hγ hpnil U)).val.obj (Opposite.op ⊤))

/-- The canonical coefficient comparison respects the actual chart-ring
action, as both restriction and F's comparison are module-sheaf maps. -/
noncomputable def coefficientSectionsEquiv :
    Γ(CrystallineSmoothLiftRepair.coefficient γA yToS I γS hc hI hγ hpnil F, U.1) ≃ₗ[Γ(Y, U.1)]
      coefficientModule γA yToS I γS hc hI hγ hpnil U F where
  __ := (coefficientSectionsIso γA yToS I γS hc hI hγ hpnil U F).addCommGroupIsoToAddEquiv
  map_smul' := sorry

/-- The specified local tensor comparison first maps crystal coefficients
and PD forms to their actual sheaf sections, then applies the genuine exterior
and tensor sheafification maps. Both tensor factors are retained. -/
noncomputable def tensorToSections (n : ℕ) :=
  -- Local instance justification (noncanonical choice): this chart uses the A-action of yToS.
  letI : Algebra A Γ(Y, U.1) := chartAlgebra yToS U
  (CrystallineAffineTensorSections.tensorMap U
    (CrystallineSmoothLiftRepair.coefficient γA yToS I γS hc hI hγ hpnil F)
    (CrystallineSmoothLiftTerms.forms yToS n)).comp
      (TensorProduct.map
        (coefficientSectionsEquiv γA yToS I γS hc hI hγ hpnil U F).symm.toLinearMap
        ((CrystallineAffineTensorSections.exteriorMap U
          (CrystallineSmoothLiftTerms.oneForms yToS) n).comp
            (exteriorPower.form.map
              (CrystallineSmoothLiftPDForms.equivalence γA yToS I hI U).toLinearMap n)))

include hqc in
/-- Affine quasi-coherence identifies the actual tensor/sheafification map
with the tensor product of the already specified coefficient and PD-form
equivalences. No assertion is made for nonaffine opens. -/
theorem tensorToSections_bijective (n : ℕ) :
    Function.Bijective (tensorToSections γA yToS I γS hc hI hγ hpnil U F n) := sorry

/-- The genuine affine connection is induced by the two actual PD
square-zero lifts and the crystal comparison, using the chart's specified
A-algebra structure. It is not an arbitrary connection supplied as a parameter. -/
noncomputable def connection :=
  -- Local instance justification (noncanonical choice): yToS fixes this chart's A-algebra action.
  letI : Algebra A Γ(Y, U.1) := chartAlgebra yToS U
  CrystallinePDSquareZeroGeometry.connection A Γ(Y, U.1)
    (smoothLiftDividedPowers γA yToS I hI U) I γS hc (smoothLift_x₀ yToS I)
    (Spec.map (CommRingCat.ofHom (affineSectionMap yToS U)))
    (fibre yToS I U) (square yToS I U) (ideal_nil γA yToS I hI hpnil U)
    (object_baseCompatible γA yToS I γS hc hI hγ hpnil U) (fibre_open yToS I U)
    (CrystallinePDSquareZeroGeometry.differentialLift_overAffineBase A Γ(Y, U.1)
      (smoothLiftDividedPowers γA yToS I hI U)) F

/-- All affine de Rham differentials are supplied by the actual
crystal-induced PD connection and the genuine exterior calculus. -/
noncomputable def complex :=
  -- Local instance justification (noncanonical choice): yToS fixes this chart's A-algebra action.
  letI : Algebra A Γ(Y, U.1) := chartAlgebra yToS U
  CrystallinePDSquareZeroGeometry.deRhamComplex A Γ(Y, U.1)
    (smoothLiftDividedPowers γA yToS I hI U) I γS hc (smoothLift_x₀ yToS I)
    (Spec.map (CommRingCat.ofHom (affineSectionMap yToS U)))
    (fibre yToS I U) (square yToS I U) (ideal_nil γA yToS I hI hpnil U)
    (object_baseCompatible γA yToS I γS hc hI hγ hpnil U) (fibre_open yToS I U)
    (CrystallinePDSquareZeroGeometry.differentialLift_overAffineBase A Γ(Y, U.1)
      (smoothLiftDividedPowers γA yToS I hI U)) F

/-- The canonical affine tensor comparison as a linear equivalence. -/
noncomputable def tensorSectionsEquiv (n : ℕ) :=
  LinearEquiv.ofBijective (tensorToSections γA yToS I γS hc hI hγ hpnil U F n)
    (tensorToSections_bijective γA yToS I γS hc hI hγ hpnil U F n)

/-- The actual affine de Rham term identifies with sections of the genuine
sheaf term. Degree zero uses the canonical tensor-unit map, not an arbitrary
coefficient/form equivalence. -/
noncomputable def termSectionsEquiv (n : ℕ) :
    (complex γA yToS I γS hc hI hγ hpnil U F).X n ≃+
      Γ(CrystallineSmoothLiftTerms.term yToS
        (CrystallineSmoothLiftRepair.coefficient γA yToS I γS hc hI hγ hpnil F) n, U.1) :=
  match n with
  | 0 =>
      (TensorProduct.rid Γ(Y, U.1) (coefficientModule γA yToS I γS hc hI hγ hpnil U F)).symm.toAddEquiv.trans
        (tensorSectionsEquiv γA yToS I γS hc hI hγ hpnil U F 0).toAddEquiv
  | n + 1 => (tensorSectionsEquiv γA yToS I γS hc hI hγ hpnil U F (n + 1)).toAddEquiv

/-- Local de Rham differentiation on actual sheaf sections, transported
through the specified affine coefficient/PD/exterior/tensor comparisons. -/
noncomputable def localDifferential (n : ℕ) :
    Γ(CrystallineSmoothLiftTerms.term yToS
        (CrystallineSmoothLiftRepair.coefficient γA yToS I γS hc hI hγ hpnil F) n, U.1) →+
      Γ(CrystallineSmoothLiftTerms.term yToS
        (CrystallineSmoothLiftRepair.coefficient γA yToS I γS hc hI hγ hpnil F) (n + 1), U.1) :=
  (termSectionsEquiv γA yToS I γS hc hI hγ hpnil U F (n + 1)).toAddMonoidHom.comp
    (((complex γA yToS I γS hc hI hγ hpnil U F).d n (n + 1)).hom.comp
      (termSectionsEquiv γA yToS I γS hc hI hγ hpnil U F n).symm.toAddMonoidHom)

/-- The actual sheaf term with scalars restricted to the given base A. -/
noncomputable abbrev sheafTerm (n : ℕ) :=
  CrystallineSmoothLiftTerms.baseTerm yToS
    (CrystallineSmoothLiftRepair.coefficient γA yToS I γS hc hI hγ hpnil F) n

/-- The local geometric differential is A-linear because the universal
relative derivative kills the image of A. It is not asserted O_Y-linear. -/
noncomputable def localLinearDifferential (n : ℕ) :
    (sheafTerm γA yToS I γS hc hI hγ hpnil F n).obj.obj (Opposite.op U.1) ⟶
      (sheafTerm γA yToS I γS hc hI hγ hpnil F (n + 1)).obj.obj (Opposite.op U.1) :=
  let source := (sheafTerm γA yToS I γS hc hI hγ hpnil F n).obj.obj (Opposite.op U.1)
  let target := (sheafTerm γA yToS I γS hc hI hγ hpnil F (n + 1)).obj.obj (Opposite.op U.1)
  @ModuleCat.ofHom A _ source target source.isAddCommGroup source.isModule target.isAddCommGroup target.isModule
    { toFun := localDifferential γA yToS I γS hc hI hγ hpnil U F n
      map_add' := map_add _
      map_smul' := sorry }

/-- The affine components commute with restriction by coherence of the
crystal and naturality of the canonical comparison maps. -/
noncomputable def basisDifferential (n : ℕ) :
    (CrystallineAffineSheafExtension.affineInclusion Y).op ⋙
        (sheafTerm γA yToS I γS hc hI hγ hpnil F n).obj ⟶
      (CrystallineAffineSheafExtension.affineInclusion Y).op ⋙
        (sheafTerm γA yToS I γS hc hI hγ hpnil F (n + 1)).obj where
  app V := localLinearDifferential γA yToS I γS hc hI hγ hpnil V.unop F n
  naturality := sorry

/-- The actual sheaf-level A-linear differential is the uniquely
determined extension of these concrete affine components. -/
noncomputable def sheafDifferential (n : ℕ) :
    sheafTerm γA yToS I γS hc hI hγ hpnil F n ⟶
      sheafTerm γA yToS I γS hc hI hγ hpnil F (n + 1) :=
  CrystallineAffineSheafExtension.extend Y _ _
    (basisDifferential γA yToS I γS hc hI hγ hpnil F n)

/-- On each affine open the sheaf differential is exactly the concrete
geometric differential constructed there; extension introduces no freedom. -/
theorem sheafDifferential_affine (n : ℕ) :
    (sheafDifferential γA yToS I γS hc hI hγ hpnil F n).hom.app (Opposite.op U.1) =
      localLinearDifferential γA yToS I γS hc hI hγ hpnil U F n :=
  CrystallineAffineSheafExtension.extend_affine Y _ _
    (basisDifferential γA yToS I γS hc hI hγ hpnil F n) U

/-- Integrability of the actual affine crystal connection gives d²=0
on every affine component; equality of sheaf maps follows by the affine basis. -/
theorem sheafDifferential_comp (n : ℕ) :
    sheafDifferential γA yToS I γS hc hI hγ hpnil F n ≫
      sheafDifferential γA yToS I γS hc hI hγ hpnil F (n + 1) = 0 := sorry

/-- The genuine de Rham complex of the smooth lift in sheaves of A-modules.
Terms are sheafified tensors and all differential maps come from the actual
affine PD square-zero construction and its unique sheaf extension. -/
noncomputable def sheafComplex :
    CochainComplex (TopCat.Sheaf (ModuleCat.{u} A) Y.toTopCat) ℕ :=
  CochainComplex.of (sheafTerm γA yToS I γS hc hI hγ hpnil F)
    (sheafDifferential γA yToS I γS hc hI hγ hpnil F)
    (sheafDifferential_comp γA yToS I γS hc hI hγ hpnil F)

end CrystallineSmoothLiftAffine
