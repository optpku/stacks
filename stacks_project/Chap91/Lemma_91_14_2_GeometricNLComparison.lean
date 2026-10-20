/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import stacks_project.Chap91.Lemma_91_14_2_GeometricNL
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom CategoryTheory.Sheaf
open SheafOfModules.RingedSite Algebra Algebra.Extension
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Hom.GeometricNL
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

abbrev sheafBase := FreeAlgebra.Presentation.base (commInverseImageStructureSheaf f)
  (Under.mk (commInverseImageStructureSheafMap f))
abbrev sheafEvaluation := FreeAlgebra.Presentation.map (commInverseImageStructureSheaf f)
  (Under.mk (commInverseImageStructureSheafMap f))

/-- The polynomial comparison sends the geometric presentation kernel to the sheaf kernel. -/
theorem kernelComparison_mem (U : (smallEtaleSite X)ᵒᵖ) :
    -- Local instance justification (noncanonical choice): use the coefficient algebra specified by this morphism f and site object U.
    letI := inverseImageAlgebra f U
    (presentation f U).ker ≤
      (conormalIdeal (sheafEvaluation f) U).comap (polynomialComparison f U) := sorry

/-- The actual map on conormal classes induced by the polynomial comparison and
by the unit of conormal sheafification and scalar extension. -/
def conormalComponent (U : (smallEtaleSite X)ᵒᵖ) :
    cotangentObj f U ⟶ (conormalSource.{u + 1, u, u} (sheafEvaluation f)).val.obj U :=
  -- Local instance justification (noncanonical choice): use the coefficient algebra specified by this morphism f and site object U.
  letI := inverseImageAlgebra f U
  -- Local instance justification (noncanonical choice): scalar restriction is along the explicit polynomialComparison, not an ambient algebra instance.
  letI : Algebra (MvPolynomial ((commStructureSheaf X).obj.obj U)
      ((commInverseImageStructureSheaf f).obj.obj U)) ((polynomialSheaf f).obj.obj U) :=
    (polynomialComparison f U).toAlgebra
  let q := (conormalSourcePresheafUnit.{u + 1, u, u} (sheafEvaluation f)).app U
  let k := Ideal.mapCotangent (presentation f U).ker (conormalIdeal (sheafEvaluation f) U)
    (Algebra.ofId _ _) (kernelComparison_mem f U)
  ModuleCat.ofHom
    { toFun := fun x ↦ q (k (Cotangent.val x))
      map_add' := by
        intro x y
        exact (congrArg (fun z ↦ q z) (k.map_add x.val y.val)).trans
          (q.hom.map_add (k x.val) (k y.val))
      map_smul' := by intros; sorry }

def conormalPresheafComparison :
    cotangentPresheaf f ⟶ (conormalSource.{u + 1, u, u} (sheafEvaluation f)).val where
  app := conormalComponent f
  naturality := sorry

def conormalComparison : cotangentSheaf f ⟶ conormalSource.{u + 1, u, u} (sheafEvaluation f) :=
  (PresheafOfModules.sheafificationHomEquiv.{u} (𝟙 (structureSheaf X).obj)).symm
    (conormalPresheafComparison f)

/-- Send the basis vector indexed by x to d[x] in the scalar-extended relative
Kähler differentials of the canonical free-algebra sheaf. -/
def differentialsComponent (U : (smallEtaleSite X)ᵒᵖ) :
    cotangentSpaceObj f U ⟶ (conormalTensorTerm.{u + 1, u, u} (sheafBase f) (sheafEvaluation f)).val.obj U :=
  -- Local instance justification (noncanonical choice): use the coefficient algebra specified by this morphism f and site object U.
  letI := inverseImageAlgebra f U
  ModuleCat.ofHom ((presentation f U).cotangentSpaceBasis.constr
    ((commStructureSheaf X).obj.obj U) (fun x ↦
      ((extendRestrictAdj.{u + 1, u, u} (sheafEvaluation f)).unit.app
        (relativeDifferentials.{u + 1, u, u} (sheafBase f))).val.app U
          (((relativeDifferential.{u + 1, u, u} (sheafBase f)).app U).d
            ((FreeAlgebra.Presentation.generator (commInverseImageStructureSheaf f)
              (Under.mk (commInverseImageStructureSheafMap f))).hom.app U x))))

def differentialsPresheafComparison :
    cotangentSpacePresheaf f ⟶
      (conormalTensorTerm.{u + 1, u, u} (sheafBase f) (sheafEvaluation f)).val where
  app := differentialsComponent f
  naturality := sorry

def differentialsComparison : cotangentSpaceSheaf f ⟶
    conormalTensorTerm.{u + 1, u, u} (sheafBase f) (sheafEvaluation f) :=
  (PresheafOfModules.sheafificationHomEquiv.{u} (𝟙 (structureSheaf X).obj)).symm
    (differentialsPresheafComparison f)

/-- Comparison of the actual geometric and ringed-topos two-term complexes. -/
def complexComparison : naiveCotangent f ⟶
    NaiveCotangent.obj (commInverseImageStructureSheaf f)
      (Under.mk (commInverseImageStructureSheafMap f)) where
  f i := match i with
    | Int.negSucc 0 => conormalComparison f
    | Int.ofNat 0 => differentialsComparison f
    | _ => 0
  comm' := sorry

/-- Sheafification of the polynomial presheaf is the free-algebra sheaf; conormal
and differential sheafification give the component isomorphisms of this explicit map. -/
theorem complexComparison_isIso : IsIso (complexComparison f) := sorry

/-- The isomorphism is tied to the polynomial comparison, not chosen from Nonempty. -/
def complexIso : naiveCotangent f ≅
    NaiveCotangent.obj (commInverseImageStructureSheaf f)
      (Under.mk (commInverseImageStructureSheafMap f)) :=
  -- Local instance justification (proof-local temporary data): invert the explicit polynomial-induced chain map, retaining its components.
  letI := complexComparison_isIso f
  asIso (complexComparison f)

@[simp] theorem complexIso_hom : (complexIso f).hom = complexComparison f := rfl
end AlgebraicGeometry.AlgebraicSpace.Hom.GeometricNL
