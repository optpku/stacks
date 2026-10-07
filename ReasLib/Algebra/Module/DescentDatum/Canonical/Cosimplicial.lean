module

public import ReasLib.Algebra.Amitsur.CosimplicialModule.Coefficients
public import ReasLib.Algebra.Module.DescentDatum.Canonical
public import ReasLib.Algebra.Module.DescentDatum.Cosimplicial

/-!
# The cosimplicial module of canonical descent data

The cosimplicial module associated to canonical scalar-extension descent data
is naturally isomorphic to the Amitsur cosimplicial module with coefficients.
-/

@[expose] public section

noncomputable section

open CategoryTheory ModuleCat Opposite
open scoped ChangeOfRings TensorProduct TensorProduct.Right

universe u

namespace Module.DescentDatum

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The comparison in one simplex degree between the module associated to
canonical descent data and the Amitsur coefficient module. -/
noncomputable def canonicalComponentIso (M : ModuleCat.{u} R)
    (Delta : SimplexCategory) :
    Algebra.Amitsur.CosimplicialModule.eval R A
        ((canonical R A M).cosimplicial) Delta ≅
      Algebra.Amitsur.CosimplicialModule.eval R A
        (Algebra.Amitsur.coefficients R A M) Delta :=
  (ModuleCat.extendScalars
      (Algebra.Amitsur.vertex R A Delta (Fin.last Delta.len))).mapIso
        (canonicalModuleIso R A M) ≪≫
    (ModuleCat.extendScalarsComp (algebraMap R A)
      (Algebra.Amitsur.vertex R A Delta (Fin.last Delta.len))).symm.app M ≪≫
    eqToIso (congrArg (fun f ↦ (ModuleCat.extendScalars f).obj M)
      (Algebra.Amitsur.vertex_comp_algebraMap R A Delta (Fin.last Delta.len)))

/-- On pure tensors, the degreewise comparison performs the canonical
normalization from the descent realization to `(A/R)Delta ⊗[R] M`. -/
theorem canonicalComponentIso_hom_tmul (M : ModuleCat.{u} R)
    (Delta : SimplexCategory)
    (m : M) (a : A) :
    (canonicalComponentIso R A M Delta).hom
      ((1 : (Algebra.Amitsur.cosimplicialCommRing R A).obj Delta) ⊗ₜ[A,
        Algebra.Amitsur.vertex R A Delta (Fin.last Delta.len)]
          (m ⊗ₜ[R] a)) =
      (Arrow.cechConerve.ι
        (Arrow.mk (CommAlgCat.ofHom (Algebra.ofId R A))) Delta
          (Fin.last Delta.len)).hom a ⊗ₜ[R,
            algebraMap R ((Algebra.Amitsur.cosimplicialAlgebra R A).obj Delta)] m := sorry

/-- The degreewise canonical comparisons commute with every simplex map. -/
theorem canonicalComponentIso_naturality (M : ModuleCat.{u} R)
    {Delta Gamma : SimplexCategory} (beta : Delta ⟶ Gamma) :
    Algebra.Amitsur.CosimplicialModule.map R A
        ((canonical R A M).cosimplicial) beta ≫
      (ModuleCat.restrictScalars
        ((Algebra.Amitsur.cosimplicialRing R A).map beta).hom).map
          (canonicalComponentIso R A M Gamma).hom =
      (canonicalComponentIso R A M Delta).hom ≫
        Algebra.Amitsur.CosimplicialModule.map R A
          (Algebra.Amitsur.coefficients R A M) beta := sorry

/-- The canonical cosimplicial module associated to `M ⊗[R] A` is
isomorphic, over the varying Amitsur rings, to `(A/R)• ⊗[R] M`. -/
noncomputable def canonicalCosimplicialIso (M : ModuleCat.{u} R) :
    (canonical R A M).cosimplicial ≅ Algebra.Amitsur.coefficients R A M :=
  PresheafOfModules.isoMk
    (fun X ↦ canonicalComponentIso R A M (unop (unop X)))
    (fun {X Y : (SimplexCategoryᵒᵖ)ᵒᵖ} (f : X ⟶ Y) ↦
      canonicalComponentIso_naturality R A M f.unop.unop)

/-- The component of `canonicalCosimplicialIso` in each simplex degree is
`canonicalComponentIso`. -/
theorem canonicalCosimplicialIso_app (M : ModuleCat.{u} R)
    (Delta : SimplexCategory) :
    Algebra.Amitsur.CosimplicialModule.app R A
        (canonicalCosimplicialIso R A M).hom Delta =
      (canonicalComponentIso R A M Delta).hom := sorry

end Module.DescentDatum
