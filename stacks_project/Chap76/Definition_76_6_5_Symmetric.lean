module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SymmetricAlgebra.CommRing
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra
public import stacks_project.Chap76.Definition_76_6_5_Conormal

/-!
# Symmetric algebras of quasi-coherent modules on algebraic spaces

This file packages the sectionwise symmetric algebra of a quasi-coherent module
sheaf on the small étale site as a quasi-coherent `𝒪_X`-algebra.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SymmetricAlgebra

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The commutative-ring sheaf obtained by sheafifying the sectionwise symmetric-algebra
presheaf of a module sheaf on `X`. -/
noncomputable def sheaf (F : X.Modules) :
    CategoryTheory.Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  (presheafToSheaf (smallEtaleTopology X) CommRingCat.{u}).obj
    (PresheafOfModules.SymmetricAlgebra.commRingPresheaf
      (commRingStructureSheaf X).obj (Modules.toComm F).val)

/-- The sheaf of `SymmetricAlgebra.sheaf F` is the sheafification of the sectionwise
symmetric algebra. -/
theorem sheaf_eq (F : X.Modules) :
    sheaf F =
      (presheafToSheaf (smallEtaleTopology X) CommRingCat.{u}).obj
        (PresheafOfModules.SymmetricAlgebra.commRingPresheaf
          (commRingStructureSheaf X).obj (Modules.toComm F).val) :=
  rfl

/-- The canonical structure map from `𝒪_X` to the symmetric-algebra sheaf of `F`. -/
noncomputable def structureMap (F : X.Modules) :
    commRingStructureSheaf X ⟶ sheaf F :=
  CategoryTheory.Sheaf.homEquiv.symm
    (PresheafOfModules.SymmetricAlgebra.commRingUnit
        (commRingStructureSheaf X).obj (Modules.toComm F).val ≫
      toSheafify (smallEtaleTopology X)
        (PresheafOfModules.SymmetricAlgebra.commRingPresheaf
          (commRingStructureSheaf X).obj (Modules.toComm F).val))

/-- The structure map of the symmetric-algebra sheaf is the sheafified unit of the
sectionwise symmetric algebra. -/
theorem structureMap_eq (F : X.Modules) :
    structureMap F =
      CategoryTheory.Sheaf.homEquiv.symm
        (PresheafOfModules.SymmetricAlgebra.commRingUnit
            (commRingStructureSheaf X).obj (Modules.toComm F).val ≫
          toSheafify (smallEtaleTopology X)
            (PresheafOfModules.SymmetricAlgebra.commRingPresheaf
              (commRingStructureSheaf X).obj (Modules.toComm F).val)) :=
  rfl

/-- The symmetric-algebra sheaf of `F`, regarded as an algebra object under `𝒪_X`. -/
noncomputable def under (F : X.Modules) : Under (commRingStructureSheaf X) :=
  Under.mk (structureMap F)

/-- `under F` is `Under.mk` of the symmetric-algebra structure map. -/
theorem under_eq (F : X.Modules) : under F = Under.mk (structureMap F) :=
  rfl

/-- The `𝒪_X`-module underlying the symmetric-algebra object `under F`. -/
noncomputable def underlyingModule (F : X.Modules) : X.Modules :=
  Modules.ofComm
    ((restrictionAlong (under F).hom).obj
      (unitModule (smallEtaleTopology X) (under F).right))

/-- The module underlying the symmetric-algebra object is the restriction of its unit
module along the structure map. -/
theorem underlyingModule_eq (F : X.Modules) :
    underlyingModule F =
      Modules.ofComm
        ((restrictionAlong (under F).hom).obj
          (unitModule (smallEtaleTopology X) (under F).right)) :=
  rfl

/-- The module underlying the symmetric-algebra object of a quasi-coherent module is
quasi-coherent. -/
theorem underlyingModule_isQuasicoherent (F : X.Modules) [F.IsQuasicoherent] :
    (underlyingModule F).IsQuasicoherent :=
  sorry

/-- The symmetric algebra of a quasi-coherent `𝒪_X`-module, as a quasi-coherent
`𝒪_X`-algebra. -/
noncomputable def qcAlgebra (F : X.Modules) [F.IsQuasicoherent] : X.QcAlgebraUnder where
  obj := under F
  property := underlyingModule_isQuasicoherent F

/-- The underlying algebra object of `qcAlgebra F` is `under F`. -/
theorem qcAlgebra_obj (F : X.Modules) [F.IsQuasicoherent] :
    (qcAlgebra F).obj = under F :=
  rfl

/-- The right-hand sheaf of `qcAlgebra F` is `sheaf F`. -/
theorem qcAlgebra_sheaf (F : X.Modules) [F.IsQuasicoherent] :
    (qcAlgebra F).obj.right = sheaf F :=
  rfl

/-- The objectwise symmetric-algebra map induced by a module-sheaf morphism into the
underlying module of a quasi-coherent algebra. -/
noncomputable def liftApp (F : X.Modules) (A : X.QcAlgebraUnder)
    (f : Modules.toComm F ⟶
      (restrictionAlong A.obj.hom).obj
        (unitModule (smallEtaleTopology X) (QcAlgebraUnder.sheaf A)))
    (U : (smallEtaleSite X)ᵒᵖ) :
    PresheafOfModules.SymmetricAlgebra.commRingObj
        (commRingStructureSheaf X).obj (Modules.toComm F).val U ⟶
      A.obj.right.obj.obj U :=
  -- Local instance justification (proof-local temporary data): sectionwise Algebra from A.obj.hom.app U is not a global algebra on the sheaf
  letI : Algebra ((commRingStructureSheaf X).obj.obj U) (A.obj.right.obj.obj U) :=
    (InducedCategory.Hom.hom A.obj.hom).app U |>.hom.toAlgebra
  CommRingCat.ofHom
    (_root_.SymmetricAlgebra.lift
      (PresheafOfModules.SymmetricAlgebra.homApp
        (commRingStructureSheaf X).obj f.val U).hom).toRingHom

/-- The objectwise symmetric-algebra lifts commute with restriction of sections. -/
theorem liftPresheaf_naturality (F : X.Modules) (A : X.QcAlgebraUnder)
    (f : Modules.toComm F ⟶
      (restrictionAlong A.obj.hom).obj
        (unitModule (smallEtaleTopology X) (QcAlgebraUnder.sheaf A)))
    {U V : (smallEtaleSite X)ᵒᵖ} (g : U ⟶ V) :
    (PresheafOfModules.SymmetricAlgebra.commRingPresheaf
          (commRingStructureSheaf X).obj (Modules.toComm F).val).map g ≫
        liftApp F A f V =
      liftApp F A f U ≫ A.obj.right.obj.map g :=
  sorry

/-- The sectionwise symmetric-algebra lifts form a morphism of presheaves of commutative
rings. -/
noncomputable def liftPresheaf (F : X.Modules) (A : X.QcAlgebraUnder)
    (f : Modules.toComm F ⟶
      (restrictionAlong A.obj.hom).obj
        (unitModule (smallEtaleTopology X) (QcAlgebraUnder.sheaf A))) :
    PresheafOfModules.SymmetricAlgebra.commRingPresheaf
        (commRingStructureSheaf X).obj (Modules.toComm F).val ⟶
      A.obj.right.obj where
  app U := liftApp F A f U
  naturality _ _ g := liftPresheaf_naturality F A f g

/-- The morphism of commutative-ring sheaves obtained by descending the sectionwise
symmetric-algebra lift through sheafification. -/
noncomputable def liftSheaf (F : X.Modules) (A : X.QcAlgebraUnder)
    (f : Modules.toComm F ⟶
      (restrictionAlong A.obj.hom).obj
        (unitModule (smallEtaleTopology X) (QcAlgebraUnder.sheaf A))) :
    sheaf F ⟶ A.obj.right :=
  ⟨sheafifyLift (smallEtaleTopology X) (liftPresheaf F A f) A.obj.right.property⟩

/-- The symmetric-algebra lift commutes with the structure maps from the structure sheaf. -/
theorem lift_comp_structureMap (F : X.Modules) [F.IsQuasicoherent] (A : X.QcAlgebraUnder)
    (f : Modules.toComm F ⟶
      (restrictionAlong A.obj.hom).obj
        (unitModule (smallEtaleTopology X) (QcAlgebraUnder.sheaf A))) :
    structureMap F ≫ liftSheaf F A f = A.obj.hom :=
  sorry

/-- A module-sheaf map into a quasi-coherent algebra extends canonically to a morphism from
the corresponding symmetric algebra. -/
noncomputable def lift (F : X.Modules) [F.IsQuasicoherent] (A : X.QcAlgebraUnder)
    (f : Modules.toComm F ⟶
      (restrictionAlong A.obj.hom).obj
        (unitModule (smallEtaleTopology X) (QcAlgebraUnder.sheaf A))) :
    qcAlgebra F ⟶ A :=
  ⟨Under.homMk (liftSheaf F A f) (lift_comp_structureMap F A f)⟩


end AlgebraicGeometry.AlgebraicSpace.SymmetricAlgebra
