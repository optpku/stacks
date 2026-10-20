module

public import ReasLib.Algebra.Category.ModuleCat.ExteriorAlgebra.Decomposition.RestrictScalars
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Coproduct
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorAlgebra
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.DegreeOne
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Total
import Mathlib.Tactic.CrossRefAttribute

/-!
# Decomposition of exterior-algebra presheaves

The sectionwise exterior-algebra presheaf is naturally the coproduct of its sectionwise exterior
powers. Its objectwise isomorphism is assembled from the explicit `ModuleCat` decomposition and
the evaluation isomorphism for coproducts of module presheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace PresheafOfModules.ExteriorAlgebra

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- The explicit sectionwise decomposition of an exterior algebra into exterior powers. -/
@[stacks 01CF "sectionwise exterior-algebra decomposition"]
noncomputable def sectionIso
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    obj O F U ≅ ((ExteriorPower.Total.functor O).obj F).obj U :=
  ModuleCat.exteriorAlgebra.decompositionIso (sectionObj O F U) ≪≫
    (PresheafOfModules.Coproduct.evaluationIso
      (fun n : ℕ ↦ ExteriorPower.presheaf O F n) U).symm

/-- The inverse sectionwise decomposition first evaluates the presheaf coproduct and then
reassembles the exterior algebra. -/
theorem sectionIso_inv
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (sectionIso O F U).inv =
      (PresheafOfModules.Coproduct.evaluationIso
        (fun n : ℕ ↦ ExteriorPower.presheaf O F n) U).hom ≫
        (ModuleCat.exteriorAlgebra.decompositionIso (sectionObj O F U)).inv := sorry

/-- The sectionwise decomposition commutes with restriction morphisms. -/
theorem sectionIso_naturality
    (F : PresheafOfModules.{w} (RingPresheaf O))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    map O F f ≫
        (ModuleCat.restrictScalars (O.map f).hom).map
          (sectionIso O F V).hom =
      (sectionIso O F U).hom ≫
        ((ExteriorPower.Total.functor O).obj F).map f := sorry

/-- The sectionwise exterior-algebra presheaf is the total exterior-power presheaf. -/
@[stacks 01CF "exterior-algebra presheaf decomposition"]
noncomputable def decompositionIso
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    presheaf O F ≅ (ExteriorPower.Total.functor O).obj F :=
  PresheafOfModules.isoMk (sectionIso O F)
    (fun _ _ f ↦ sectionIso_naturality O F f)

/-- A component of the presheaf decomposition is the explicit sectionwise decomposition. -/
@[simp]
theorem decompositionIso_hom_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (decompositionIso O F).hom.app U = (sectionIso O F U).hom := sorry

/-- An inverse component of the presheaf decomposition is the inverse sectionwise
decomposition. -/
@[simp]
theorem decompositionIso_inv_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) (U : Cᵒᵖ) :
    (decompositionIso O F).inv.app U = (sectionIso O F U).inv := sorry

/-- Restriction compatibility for the homogeneous inclusion into the exterior algebra. -/
theorem powerι_app_naturality
    (F : PresheafOfModules.{w} (RingPresheaf O)) (n : ℕ)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    ExteriorPower.map O F n f ≫
        (ModuleCat.restrictScalars (O.map f).hom).map
          (ModuleCat.exteriorAlgebra.powerι (sectionObj O F V) n) =
      ModuleCat.exteriorAlgebra.powerι (sectionObj O F U) n ≫
        map O F f := sorry

/-- The degree-`n` homogeneous inclusion into the sectionwise exterior-algebra presheaf. -/
@[stacks 01CF "homogeneous inclusion into an exterior-algebra presheaf"]
noncomputable def powerι
    (F : PresheafOfModules.{w} (RingPresheaf O)) (n : ℕ) :
    ExteriorPower.presheaf O F n ⟶ presheaf O F where
  app U := ModuleCat.exteriorAlgebra.powerι (sectionObj O F U) n
  naturality f := powerι_app_naturality O F n f

/-- Exterior-power presheaf maps commute with homogeneous inclusions. -/
@[reassoc]
theorem map_powerι
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) (n : ℕ) :
    ExteriorPower.hom O f n ≫ powerι O G n =
      powerι O F n ≫ hom O f := sorry

/-- For fixed degree, homogeneous inclusion is natural in the module presheaf. -/
@[stacks 01CF "natural homogeneous inclusion into an exterior-algebra presheaf"]
noncomputable def powerιNatTrans (n : ℕ) :
    ExteriorPower.functor O n ⟶ ExteriorAlgebra.functor O where
  app F := powerι O F n
  naturality _ _ f := map_powerι O f n

/-- A component of the fixed-degree presheaf inclusion is `powerι`. -/
@[simp]
theorem powerιNatTrans_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) (n : ℕ) :
    (powerιNatTrans O n).app F = powerι O F n := sorry

/-- Under the presheaf decomposition, a homogeneous inclusion is the coproduct inclusion. -/
@[reassoc (attr := simp)]
theorem powerι_decompositionIso_hom
    (F : PresheafOfModules.{w} (RingPresheaf O)) (n : ℕ) :
    powerι O F n ≫ (decompositionIso O F).hom =
      Limits.Sigma.ι
        (fun n : ℕ ↦ ExteriorPower.presheaf O F n) n := sorry

/-- The degree-one exterior-power inclusion is the usual exterior-algebra presheaf generator. -/
@[reassoc (attr := simp)]
theorem degreeOne_powerι
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    ExteriorPower.degreeOne O F ≫ powerι O F 1 = ι O F := sorry

/-- Under the total decomposition, the usual presheaf generator lands in degree one. -/
@[reassoc (attr := simp)]
theorem ι_decompositionIso_hom
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    ι O F ≫ (decompositionIso O F).hom =
      ExteriorPower.degreeOne O F ≫
        Limits.Sigma.ι
          (fun n : ℕ ↦ ExteriorPower.presheaf O F n) 1 := sorry

/-- The exterior-algebra presheaf decomposition is natural in the module presheaf. -/
theorem decompositionIso_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) :
    hom O f ≫ (decompositionIso O G).hom =
      (decompositionIso O F).hom ≫
        (ExteriorPower.Total.functor O).map f := sorry

/-- The inverse exterior-algebra decomposition is natural in the module presheaf. -/
@[stacks 01CF "inverse naturality of the exterior-algebra presheaf decomposition"]
theorem decompositionIso_inv_naturality
    {F G : PresheafOfModules.{w} (RingPresheaf O)} (f : F ⟶ G) :
    (ExteriorPower.Total.functor O).map f ≫ (decompositionIso O G).inv =
      (decompositionIso O F).inv ≫ hom O f := sorry

/-- The forward decomposition maps form a natural transformation from exterior algebras to total
exterior powers. -/
@[stacks 01CF "forward exterior-algebra decomposition natural transformation"]
noncomputable def functorNatTrans :
    ExteriorAlgebra.functor O ⟶ ExteriorPower.Total.functor O where
  app F := (decompositionIso O F).hom
  naturality _ _ f := decompositionIso_naturality O f

/-- The inverse decomposition maps form the inverse natural transformation. -/
@[stacks 01CF "inverse exterior-algebra decomposition natural transformation"]
noncomputable def functorInvNatTrans :
    ExteriorPower.Total.functor O ⟶ ExteriorAlgebra.functor O where
  app F := (decompositionIso O F).inv
  naturality _ _ f := decompositionIso_inv_naturality O f

/-- A component of the forward decomposition natural transformation is the objectwise
decomposition map. -/
@[simp, stacks 01CF "forward exterior-algebra decomposition natural transformation component"]
theorem functorNatTrans_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (functorNatTrans O).app F = (decompositionIso O F).hom := sorry

/-- A component of the inverse decomposition natural transformation is the objectwise inverse
decomposition map. -/
@[simp, stacks 01CF "inverse exterior-algebra decomposition natural transformation component"]
theorem functorInvNatTrans_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (functorInvNatTrans O).app F = (decompositionIso O F).inv := sorry

/-- The forward decomposition natural transformation followed by its inverse is the identity. -/
@[simp, stacks 01CF "exterior-algebra decomposition natural transformation forward-inverse law"]
theorem functorNatTrans_hom_inv_id :
    functorNatTrans O ≫ functorInvNatTrans O = 𝟙 _ := sorry

/-- The inverse decomposition natural transformation followed by its forward map is the
identity. -/
@[simp, stacks 01CF "exterior-algebra decomposition natural transformation inverse-forward law"]
theorem functorNatTrans_inv_hom_id :
    functorInvNatTrans O ≫ functorNatTrans O = 𝟙 _ := sorry

/-- Exterior-algebra presheaves are naturally total exterior-power presheaves. -/
@[stacks 01CF "natural exterior-algebra presheaf decomposition"]
noncomputable def functorIso :
    ExteriorAlgebra.functor O ≅ ExteriorPower.Total.functor O :=
  { hom := functorNatTrans O
    inv := functorInvNatTrans O
    hom_inv_id := functorNatTrans_hom_inv_id O
    inv_hom_id := functorNatTrans_inv_hom_id O }

/-- The forward natural transformation of `functorIso` is explicit. -/
@[simp, stacks 01CF "exterior-algebra decomposition natural isomorphism hom"]
theorem functorIso_hom :
    (functorIso O).hom = functorNatTrans O := sorry

/-- The inverse natural transformation of `functorIso` is explicit. -/
@[simp, stacks 01CF "exterior-algebra decomposition natural isomorphism inverse"]
theorem functorIso_inv :
    (functorIso O).inv = functorInvNatTrans O := sorry

/-- A component of `functorIso` is the objectwise exterior-algebra decomposition. -/
@[simp, stacks 01CF "exterior-algebra decomposition natural isomorphism component"]
theorem functorIso_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (functorIso O).app F = decompositionIso O F := sorry

/-- The forward component of `functorIso` is the objectwise decomposition map. -/
@[simp, stacks 01CF "exterior-algebra decomposition natural isomorphism hom component"]
theorem functorIso_hom_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (functorIso O).hom.app F = (decompositionIso O F).hom := sorry

/-- The inverse component of `functorIso` is the objectwise inverse decomposition map. -/
@[simp, stacks 01CF "exterior-algebra decomposition natural isomorphism inverse component"]
theorem functorIso_inv_app
    (F : PresheafOfModules.{w} (RingPresheaf O)) :
    (functorIso O).inv.app F = (decompositionIso O F).inv := sorry

end PresheafOfModules.ExteriorAlgebra
