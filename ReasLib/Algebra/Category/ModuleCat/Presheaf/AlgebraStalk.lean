/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorAlgebra.Ring
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SymmetricAlgebra.CommRing
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.TensorAlgebra.Ring
public import ReasLib.Topology.Sheaves.Stalks.Filtered
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebra presheaves and stalks

This file constructs the canonical comparisons from stalks of sectionwise tensor, symmetric,
and exterior algebras to the corresponding algebra of the stalk module.  All constructions are
owned at the module-presheaf layer and are independent of sheafification and ringed spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace PresheafOfModules.AlgebraStalk

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}

/-- The underlying ring of a commutative-ring presheaf stalk is canonically the stalk of its
underlying ring-valued presheaf. -/
noncomputable abbrev baseStalkIso (R : X.Presheaf CommRingCat.{u}) (x : X) :
    (forget₂ CommRingCat RingCat).obj (R.stalk x) ≅
      TopCat.Presheaf.filteredStalk (C := RingCat.{u}) x
        (CategoryTheory.Presheaf.ringPresheafOfComm R) :=
  TopCat.Presheaf.stalkCompIsoOf x (forget₂ CommRingCat RingCat) R

/-- The structural ring map from the base stalk to the stalk of a ring-valued algebra
presheaf. -/
noncomputable def structureMap (A : X.Presheaf RingCat.{u})
    (η : CategoryTheory.Presheaf.ringPresheafOfComm R ⟶ A) (x : X) :
    R.stalk x →+* TopCat.Presheaf.filteredStalk (C := RingCat.{u}) x A :=
  ((baseStalkIso R x).hom ≫
    (TopCat.Presheaf.filteredStalkFunctor (C := RingCat.{u}) x).map η).hom

/-- A comparison between a ring-valued presheaf and the additive presheaf underlying a module
presheaf induces the corresponding comparison of stalks. -/
noncomputable def sourceAddIso (A : X.Presheaf RingCat.{u})
    (M : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R))
    (e : A ⋙ forget₂ RingCat AddCommGrpCat.{u} ≅ M.presheaf) (x : X) :
    (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj
        (PresheafOfModules.stalkModuleCatOfCommRing M x) ≅
      (forget₂ RingCat AddCommGrpCat.{u}).obj
        (TopCat.Presheaf.filteredStalk (C := RingCat.{u}) x A) :=
  (TopCat.Presheaf.filteredStalkFunctor (C := AddCommGrpCat.{u}) x).mapIso e.symm ≪≫
    (TopCat.Presheaf.stalkCompIsoOf x (forget₂ RingCat AddCommGrpCat) A).symm

/-- A comparison between a commutative-ring-valued presheaf and the additive presheaf
underlying a module presheaf induces the corresponding comparison of stalks. -/
noncomputable def sourceAddIsoOfComm (A : X.Presheaf CommRingCat.{u})
    (M : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R))
    (e : A ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u} ≅
      M.presheaf) (x : X) :
    (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj
        (PresheafOfModules.stalkModuleCatOfCommRing M x) ≅
      (forget₂ RingCat AddCommGrpCat.{u}).obj
        ((forget₂ CommRingCat RingCat).obj
          (TopCat.Presheaf.filteredStalk (C := CommRingCat.{u}) x A)) :=
  (TopCat.Presheaf.filteredStalkFunctor (C := AddCommGrpCat.{u}) x).mapIso e.symm ≪≫
    (TopCat.Presheaf.stalkCompIsoOf x
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) A).symm

end PresheafOfModules.AlgebraStalk

namespace PresheafOfModules.TensorAlgebra.Stalk

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
variable (F : PresheafOfModules
  (CategoryTheory.Presheaf.ringPresheafOfComm R)) (x : X)

/-- The stalk of the sectionwise tensor-algebra presheaf. -/
abbrev source : ModuleCat (R.stalk x) :=
  PresheafOfModules.stalkModuleCatOfCommRing
    (PresheafOfModules.TensorAlgebra.presheaf R F) x

/-- The tensor algebra of the stalk module. -/
abbrev target : ModuleCat (R.stalk x) :=
  (PresheafOfModules.stalkModuleCatOfCommRing F x).tensorAlgebra

/-- The stalk of the ring-valued sectionwise tensor-algebra presheaf. -/
noncomputable abbrev sourceRing : RingCat.{u} :=
  TopCat.Presheaf.filteredStalk (C := RingCat.{u}) x
    (PresheafOfModules.TensorAlgebra.ringPresheaf R F)

/-- The structural ring map from the base stalk to the tensor-algebra ring stalk. -/
noncomputable abbrev sourceStructureMap : R.stalk x →+* sourceRing F x :=
  PresheafOfModules.AlgebraStalk.structureMap
    (PresheafOfModules.TensorAlgebra.ringPresheaf R F)
    (PresheafOfModules.TensorAlgebra.ringUnit R F) x

/-- The image of the base stalk is central in the tensor-algebra ring stalk. -/
theorem sourceStructureMap_commutes (r : R.stalk x) (a : sourceRing F x) :
    sourceStructureMap F x r * a = a * sourceStructureMap F x r := sorry

/-- The tensor-algebra ring stalk is canonically an algebra over the base stalk. -/
noncomputable instance sourceAlgebra : Algebra (R.stalk x) (sourceRing F x) :=
  RingHom.toAlgebra' (sourceStructureMap F x) (sourceStructureMap_commutes F x)

/-- The tensor-algebra ring stalk, regarded as a module over the base stalk. -/
noncomputable abbrev sourceModule : ModuleCat (R.stalk x) :=
  ModuleCat.of (R.stalk x) (sourceRing F x)

/-- The additive stalk of the module-valued tensor-algebra presheaf agrees with the underlying
additive group of the ring-valued stalk. -/
noncomputable def sourceAddIso :
    (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (source F x) ≅
      (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (sourceModule F x) :=
  PresheafOfModules.AlgebraStalk.sourceAddIso
    (PresheafOfModules.TensorAlgebra.ringPresheaf R F)
    (PresheafOfModules.TensorAlgebra.presheaf R F)
    (PresheafOfModules.TensorAlgebra.addCommGrpPresheafIso R F) x

/-- The additive tensor-algebra stalk comparison respects the base-stalk scalar action. -/
theorem sourceAddIso_smul (r : R.stalk x) :
    (sourceAddIso F x).hom ≫ (sourceModule F x).smul r =
      (source F x).smul r ≫ (sourceAddIso F x).hom := sorry

/-- The module-valued tensor-algebra stalk and the module underlying its ring stalk are
canonically isomorphic. -/
noncomputable def sourceLinearIso : source F x ≅ sourceModule F x :=
  ModuleCat.isoMk (sourceAddIso F x) (sourceAddIso_smul F x)

/-- The degree-one generator map from the stalk module into the tensor-algebra ring stalk. -/
noncomputable def stalkGenerator :
    PresheafOfModules.stalkModuleCatOfCommRing F x ⟶ sourceModule F x :=
  PresheafOfModules.stalkMapOfCommRing
      (PresheafOfModules.TensorAlgebra.ι R F) x ≫
    (sourceLinearIso F x).hom

/-- The universal tensor-algebra lift into the ring-valued tensor-algebra stalk. -/
noncomputable def comparisonInvLift : target F x ⟶ sourceModule F x :=
  ModuleCat.ofHom
    (TensorAlgebra.lift (R.stalk x) (stalkGenerator F x).hom).toLinearMap

/-- The degree-one tensor-algebra generator determined by the germ of a section. -/
def germGenerator (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) : target F x :=
  ModuleCat.tensorAlgebra.ι (PresheafOfModules.stalkModuleCatOfCommRing F x)
    (TopCat.Presheaf.germ F.presheaf U x hx m)

/-- The neighborhood leg from a sectionwise tensor algebra to the tensor algebra of the stalk
module. -/
noncomputable def leg (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙
      (PresheafOfModules.TensorAlgebra.presheaf R F).presheaf).obj U) ⟶
      (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target F x) :=
  AddCommGrpCat.ofHom
    (ModuleCat.tensorAlgebra.mapRestrictScalars
      (R.germ U.unop.1 x U.unop.2).hom
      (PresheafOfModules.germToStalk F x U.unop.1 U.unop.2)).hom.toAddMonoidHom

/-- A tensor-algebra neighborhood leg sends a degree-one generator to the generator of its
germ. -/
theorem leg_ι (U : (OpenNhds x)ᵒᵖ)
    (m : F.obj ((OpenNhds.inclusion x).op.obj U)) :
    leg F x U
        (ModuleCat.tensorAlgebra.ι
          (PresheafOfModules.TensorAlgebra.sectionObj R F
            ((OpenNhds.inclusion x).op.obj U)) m) =
      germGenerator F x U.unop.1 U.unop.2 m := sorry

/-- The tensor-algebra neighborhood legs are compatible with restriction. -/
theorem leg_naturality {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙
      (PresheafOfModules.TensorAlgebra.presheaf R F).presheaf).map i) ≫
        leg F x V =
      leg F x U := sorry

/-- The cocone of neighborhood tensor algebras with vertex the tensor algebra of the stalk
module. -/
noncomputable def cocone :
    Cocone ((OpenNhds.inclusion x).op ⋙
      (PresheafOfModules.TensorAlgebra.presheaf R F).presheaf) where
  pt := (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target F x)
  ι :=
    { app := leg F x
      naturality := fun _ _ i ↦ leg_naturality F x i }

/-- The additive map from the stalk of the sectionwise tensor algebra to the tensor algebra of
the stalk module. -/
noncomputable def addMap :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModules.TensorAlgebra.presheaf R F).presheaf x ⟶
      (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target F x) :=
  colimit.desc _ (cocone F x)

/-- The additive tensor-algebra stalk map preserves addition. -/
theorem addMap_add (m n : source F x) :
    addMap F x (m + n) = addMap F x m + addMap F x n := sorry

/-- The additive tensor-algebra stalk map is linear over the stalk ring. -/
theorem addMap_smul (r : R.stalk x) (m : source F x) :
    addMap F x (r • m) =
      HSMul.hSMul (α := R.stalk x) (β := target F x) r (addMap F x m) := sorry

/-- The canonical comparison from the stalk of the sectionwise tensor algebra to the tensor
algebra of the stalk module. -/
noncomputable def comparison : source F x ⟶ target F x :=
  ModuleCat.ofHom
    { toFun := addMap F x
      map_add' := addMap_add F x
      map_smul' := addMap_smul F x }

/-- The tensor-algebra stalk comparison sends the germ of a degree-one generator to the
generator of the corresponding module germ. -/
theorem comparison_germ_ι (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    comparison F x
        (TopCat.Presheaf.germ
          (PresheafOfModules.TensorAlgebra.presheaf R F).presheaf U x hx
          (ModuleCat.tensorAlgebra.ι
            (PresheafOfModules.TensorAlgebra.sectionObj R F (op U)) m)) =
      germGenerator F x U hx m := sorry

/-- The explicit inverse comparison obtained from the tensor-algebra universal property. -/
@[stacks 01CH "inverse module-presheaf tensor algebra stalk comparison"]
noncomputable def comparisonInv : target F x ⟶ source F x :=
  comparisonInvLift F x ≫ (sourceLinearIso F x).inv

/-- The forward tensor-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "module-presheaf tensor algebra stalk comparison on degree one"]
theorem comparison_ι :
    PresheafOfModules.stalkMapOfCommRing
        (PresheafOfModules.TensorAlgebra.ι R F) x ≫ comparison F x =
      ModuleCat.tensorAlgebra.ιHom
        (PresheafOfModules.stalkModuleCatOfCommRing F x) := sorry

/-- The inverse tensor-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "inverse module-presheaf tensor algebra stalk comparison on degree one"]
theorem comparisonInv_ι :
    ModuleCat.tensorAlgebra.ιHom
        (PresheafOfModules.stalkModuleCatOfCommRing F x) ≫ comparisonInv F x =
      PresheafOfModules.stalkMapOfCommRing
        (PresheafOfModules.TensorAlgebra.ι R F) x := sorry

/-- The inverse tensor-algebra stalk comparison sends a generator of a germ to the germ of the
corresponding sectionwise generator. -/
@[simp, stacks 01CH "inverse tensor algebra stalk comparison on germ generators"]
theorem comparisonInv_germGenerator (U : Opens X) (hx : x ∈ U)
    (m : F.obj (op U)) :
    comparisonInv F x (germGenerator F x U hx m) =
      TopCat.Presheaf.germ
        (PresheafOfModules.TensorAlgebra.presheaf R F).presheaf U x hx
        (ModuleCat.tensorAlgebra.ι
          (PresheafOfModules.TensorAlgebra.sectionObj R F (op U)) m) := sorry

/-- The forward tensor-algebra stalk comparison followed by its explicit inverse is the
identity. -/
@[simp, stacks 01CH "tensor algebra stalk comparison component right inverse"]
theorem comparison_comp_comparisonInv :
    comparison F x ≫ comparisonInv F x = 𝟙 (source F x) := sorry

/-- The explicit inverse tensor-algebra stalk comparison followed by the forward comparison is
the identity. -/
@[simp, stacks 01CH "tensor algebra stalk comparison component left inverse"]
theorem comparisonInv_comp_comparison :
    comparisonInv F x ≫ comparison F x = 𝟙 (target F x) := sorry

/-- Stalks commute with sectionwise tensor algebras of module presheaves. -/
instance comparison_isIso : IsIso (comparison F x) := sorry

/-- The canonical isomorphism from the stalk of the sectionwise tensor algebra to the tensor
algebra of the stalk module. -/
@[stacks 01CH "module-presheaf tensor algebra stalk comparison isomorphism"]
noncomputable def comparisonIso : source F x ≅ target F x where
  hom := comparison F x
  inv := comparisonInv F x
  hom_inv_id := comparison_comp_comparisonInv F x
  inv_hom_id := comparisonInv_comp_comparison F x

/-- The forward map of `comparisonIso` is the explicit tensor-algebra comparison. -/
@[simp, stacks 01CH "tensor algebra stalk comparison isomorphism forward projection"]
theorem comparisonIso_hom : (comparisonIso F x).hom = comparison F x := sorry

/-- The inverse map of `comparisonIso` is the explicit tensor-algebra universal lift. -/
@[simp, stacks 01CH "tensor algebra stalk comparison isomorphism inverse projection"]
theorem comparisonIso_inv : (comparisonIso F x).inv = comparisonInv F x := sorry

/-- The explicit inverse tensor-algebra stalk comparison is an isomorphism. -/
instance comparisonInv_isIso : IsIso (comparisonInv F x) := sorry

/-- The presheaf tensor-algebra stalk comparison is natural in the module presheaf. -/
theorem comparison_naturality
    {F G : PresheafOfModules
      (CategoryTheory.Presheaf.ringPresheafOfComm R)} (f : F ⟶ G) (x : X) :
    CommSq
      (PresheafOfModules.stalkMapOfCommRing
        (PresheafOfModules.TensorAlgebra.hom R f) x)
      (comparison F x)
      (comparison G x)
      (ModuleCat.tensorAlgebra.map
        (PresheafOfModules.stalkMapOfCommRing f x)) := sorry

/-- The explicit inverse tensor-algebra stalk comparison is natural in the module presheaf. -/
@[stacks 01CH "inverse module-presheaf tensor algebra stalk comparison naturality"]
theorem comparisonInv_naturality
    {F G : PresheafOfModules
      (CategoryTheory.Presheaf.ringPresheafOfComm R)} (f : F ⟶ G) (x : X) :
    ModuleCat.tensorAlgebra.map
        (PresheafOfModules.stalkMapOfCommRing f x) ≫ comparisonInv G x =
      comparisonInv F x ≫
        PresheafOfModules.stalkMapOfCommRing
          (PresheafOfModules.TensorAlgebra.hom R f) x := sorry

/-- The presheaf tensor-algebra stalk isomorphism is natural in the module presheaf. -/
@[stacks 01CH "module-presheaf tensor algebra stalk isomorphism naturality"]
theorem comparisonIso_naturality
    {F G : PresheafOfModules
      (CategoryTheory.Presheaf.ringPresheafOfComm R)} (f : F ⟶ G) (x : X) :
    (PresheafOfModules.TensorAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x).map f ≫
          (comparisonIso G x).hom =
      (comparisonIso F x).hom ≫
        (PresheafOfModules.stalkFunctorOfCommRing R x ⋙
          ModuleCat.tensorAlgebra.functor (R.stalk x)).map f := sorry

/-- The tensor-algebra stalk comparisons as a natural transformation. -/
@[stacks 01CH "module-presheaf tensor algebra stalk natural transformation"]
noncomputable def natTrans (R : X.Presheaf CommRingCat.{u}) (x : X) :
    PresheafOfModules.TensorAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x ⟶
      PresheafOfModules.stalkFunctorOfCommRing R x ⋙
        ModuleCat.tensorAlgebra.functor (R.stalk x) where
  app F := comparison F x
  naturality _ _ f := (comparison_naturality f x).w

/-- The explicit inverse tensor-algebra stalk comparisons as a natural transformation. -/
@[stacks 01CH "inverse module-presheaf tensor algebra stalk natural transformation"]
noncomputable def invNatTrans (R : X.Presheaf CommRingCat.{u}) (x : X) :
    PresheafOfModules.stalkFunctorOfCommRing R x ⋙
        ModuleCat.tensorAlgebra.functor (R.stalk x) ⟶
      PresheafOfModules.TensorAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x where
  app F := comparisonInv F x
  naturality _ _ f := comparisonInv_naturality f x

/-- A component of the forward tensor-algebra stalk natural transformation is the explicit
comparison. -/
@[simp, stacks 01CH "tensor algebra stalk natural transformation component"]
theorem natTrans_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (natTrans R x).app F = comparison F x := sorry

/-- A component of the inverse tensor-algebra stalk natural transformation is the explicit
universal-property inverse. -/
@[simp, stacks 01CH "inverse tensor algebra stalk natural transformation component"]
theorem invNatTrans_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (invNatTrans R x).app F = comparisonInv F x := sorry

/-- The tensor-algebra stalk natural transformation followed by its explicit inverse is the
identity natural transformation. -/
@[simp, stacks 01CH "tensor algebra stalk natural transformation right inverse"]
theorem natTrans_comp_invNatTrans (R : X.Presheaf CommRingCat.{u}) (x : X) :
    natTrans R x ≫ invNatTrans R x =
      𝟙 (PresheafOfModules.TensorAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x) := sorry

/-- The explicit inverse tensor-algebra stalk natural transformation followed by the forward
transformation is the identity. -/
@[simp, stacks 01CH "tensor algebra stalk natural transformation left inverse"]
theorem invNatTrans_comp_natTrans (R : X.Presheaf CommRingCat.{u}) (x : X) :
    invNatTrans R x ≫ natTrans R x =
      𝟙 (PresheafOfModules.stalkFunctorOfCommRing R x ⋙
        ModuleCat.tensorAlgebra.functor (R.stalk x)) := sorry

/-- The tensor-algebra stalk comparison natural transformation is invertible. -/
@[stacks 01CH "module-presheaf tensor algebra stalk natural transformation is invertible",
  instance]
instance natTrans_isIso (R : X.Presheaf CommRingCat.{u}) (x : X) :
    IsIso (natTrans R x) := sorry

/-- The tensor-algebra stalk comparisons as a natural isomorphism. -/
@[stacks 01CH "module-presheaf tensor algebra stalk natural isomorphism"]
noncomputable def comparisonNatIso (R : X.Presheaf CommRingCat.{u}) (x : X) :
    PresheafOfModules.TensorAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x ≅
      PresheafOfModules.stalkFunctorOfCommRing R x ⋙
        ModuleCat.tensorAlgebra.functor (R.stalk x) where
  hom := natTrans R x
  inv := invNatTrans R x
  hom_inv_id := natTrans_comp_invNatTrans R x
  inv_hom_id := invNatTrans_comp_natTrans R x

/-- A component of `comparisonNatIso` is the pointwise tensor-algebra comparison isomorphism. -/
@[simp, stacks 01CH "tensor algebra stalk natural isomorphism component"]
theorem comparisonNatIso_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (comparisonNatIso R x).app F = comparisonIso F x := sorry

/-- The forward natural transformation of `comparisonNatIso` is `natTrans`. -/
@[simp, stacks 01CH "tensor algebra stalk natural isomorphism forward projection"]
theorem comparisonNatIso_hom (R : X.Presheaf CommRingCat.{u}) (x : X) :
    (comparisonNatIso R x).hom = natTrans R x := sorry

/-- The inverse natural transformation of `comparisonNatIso` is the explicit universal-lift
comparison. -/
@[simp, stacks 01CH "tensor algebra stalk natural isomorphism inverse projection"]
theorem comparisonNatIso_inv (R : X.Presheaf CommRingCat.{u}) (x : X) :
    (comparisonNatIso R x).inv = invNatTrans R x := sorry

/-- A forward component of `comparisonNatIso` is the explicit tensor-algebra stalk
comparison. -/
@[simp, stacks 01CH "tensor algebra stalk natural isomorphism forward component"]
theorem comparisonNatIso_hom_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (comparisonNatIso R x).hom.app F = comparison F x := sorry

/-- The inverse component of `comparisonNatIso` is the inverse pointwise comparison. -/
@[simp, stacks 01CH "tensor algebra stalk natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (comparisonNatIso R x).inv.app F = comparisonInv F x := sorry

end PresheafOfModules.TensorAlgebra.Stalk

namespace PresheafOfModules.SymmetricAlgebra.Stalk

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
variable (F : PresheafOfModules
  (CategoryTheory.Presheaf.ringPresheafOfComm R)) (x : X)

/-- The stalk of the sectionwise symmetric-algebra presheaf. -/
abbrev source : ModuleCat (R.stalk x) :=
  PresheafOfModules.stalkModuleCatOfCommRing
    (PresheafOfModules.SymmetricAlgebra.presheaf R F) x

/-- The symmetric algebra of the stalk module. -/
abbrev target : ModuleCat (R.stalk x) :=
  (PresheafOfModules.stalkModuleCatOfCommRing F x).symmetricAlgebra

/-- The stalk of the commutative-ring-valued sectionwise symmetric-algebra presheaf. -/
noncomputable abbrev sourceRing : CommRingCat.{u} :=
  TopCat.Presheaf.filteredStalk (C := CommRingCat.{u}) x
    (PresheafOfModules.SymmetricAlgebra.commRingPresheaf R F)

/-- The structural ring map from the base stalk to the symmetric-algebra ring stalk. -/
noncomputable abbrev sourceStructureMap : R.stalk x →+* sourceRing F x :=
  ((TopCat.Presheaf.filteredStalkFunctor (C := CommRingCat.{u}) x).map
    (PresheafOfModules.SymmetricAlgebra.commRingUnit R F)).hom

/-- The symmetric-algebra ring stalk is canonically an algebra over the base stalk. -/
noncomputable instance sourceAlgebra : Algebra (R.stalk x) (sourceRing F x) :=
  RingHom.toAlgebra (sourceStructureMap F x)

/-- The symmetric-algebra ring stalk, regarded as a module over the base stalk. -/
noncomputable abbrev sourceModule : ModuleCat (R.stalk x) :=
  ModuleCat.of (R.stalk x) (sourceRing F x)

/-- The additive stalk of the module-valued symmetric-algebra presheaf agrees with the
underlying additive group of the commutative-ring-valued stalk. -/
noncomputable def sourceAddIso :
    (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (source F x) ≅
      (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (sourceModule F x) :=
  PresheafOfModules.AlgebraStalk.sourceAddIsoOfComm
    (PresheafOfModules.SymmetricAlgebra.commRingPresheaf R F)
    (PresheafOfModules.SymmetricAlgebra.presheaf R F)
    (PresheafOfModules.SymmetricAlgebra.addCommGrpPresheafIso R F) x

/-- The additive symmetric-algebra stalk comparison respects the base-stalk scalar action. -/
theorem sourceAddIso_smul (r : R.stalk x) :
    (sourceAddIso F x).hom ≫ (sourceModule F x).smul r =
      (source F x).smul r ≫ (sourceAddIso F x).hom := sorry

/-- The module-valued symmetric-algebra stalk and the module underlying its ring stalk are
canonically isomorphic. -/
noncomputable def sourceLinearIso : source F x ≅ sourceModule F x :=
  ModuleCat.isoMk (sourceAddIso F x) (sourceAddIso_smul F x)

/-- The degree-one generator map from the stalk module into the symmetric-algebra ring stalk. -/
noncomputable def stalkGenerator :
    PresheafOfModules.stalkModuleCatOfCommRing F x ⟶ sourceModule F x :=
  PresheafOfModules.stalkMapOfCommRing
      (PresheafOfModules.SymmetricAlgebra.ι R F) x ≫
    (sourceLinearIso F x).hom

/-- The universal symmetric-algebra lift into the commutative-ring-valued algebra stalk. -/
noncomputable def comparisonInvLift : target F x ⟶ sourceModule F x :=
  ModuleCat.ofHom
    (_root_.SymmetricAlgebra.lift (stalkGenerator F x).hom).toLinearMap

/-- The degree-one symmetric-algebra generator determined by the germ of a section. -/
def germGenerator (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) : target F x :=
  ModuleCat.symmetricAlgebra.ι (PresheafOfModules.stalkModuleCatOfCommRing F x)
    (TopCat.Presheaf.germ F.presheaf U x hx m)

/-- The neighborhood leg from a sectionwise symmetric algebra to the symmetric algebra of the
stalk module. -/
noncomputable def leg (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙
      (PresheafOfModules.SymmetricAlgebra.presheaf R F).presheaf).obj U) ⟶
      (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target F x) :=
  AddCommGrpCat.ofHom
    (ModuleCat.symmetricAlgebra.mapRestrictScalars
      (R.germ U.unop.1 x U.unop.2).hom
      (PresheafOfModules.germToStalk F x U.unop.1 U.unop.2)).hom.toAddMonoidHom

/-- A symmetric-algebra neighborhood leg sends a degree-one generator to the generator of its
germ. -/
theorem leg_ι (U : (OpenNhds x)ᵒᵖ)
    (m : F.obj ((OpenNhds.inclusion x).op.obj U)) :
    leg F x U
        (ModuleCat.symmetricAlgebra.ι
          (PresheafOfModules.SymmetricAlgebra.sectionObj R F
            ((OpenNhds.inclusion x).op.obj U)) m) =
      germGenerator F x U.unop.1 U.unop.2 m := sorry

/-- The symmetric-algebra neighborhood legs are compatible with restriction. -/
theorem leg_naturality {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙
      (PresheafOfModules.SymmetricAlgebra.presheaf R F).presheaf).map i) ≫
        leg F x V =
      leg F x U := sorry

/-- The cocone of neighborhood symmetric algebras with vertex the symmetric algebra of the
stalk module. -/
noncomputable def cocone :
    Cocone ((OpenNhds.inclusion x).op ⋙
      (PresheafOfModules.SymmetricAlgebra.presheaf R F).presheaf) where
  pt := (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target F x)
  ι :=
    { app := leg F x
      naturality := fun _ _ i ↦ leg_naturality F x i }

/-- The additive map from the stalk of the sectionwise symmetric algebra to the symmetric
algebra of the stalk module. -/
noncomputable def addMap :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModules.SymmetricAlgebra.presheaf R F).presheaf x ⟶
      (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target F x) :=
  colimit.desc _ (cocone F x)

/-- The additive symmetric-algebra stalk map preserves addition. -/
theorem addMap_add (m n : source F x) :
    addMap F x (m + n) = addMap F x m + addMap F x n := sorry

/-- The additive symmetric-algebra stalk map is linear over the stalk ring. -/
theorem addMap_smul (r : R.stalk x) (m : source F x) :
    addMap F x (r • m) =
      HSMul.hSMul (α := R.stalk x) (β := target F x) r (addMap F x m) := sorry

/-- The canonical comparison from the stalk of the sectionwise symmetric algebra to the
symmetric algebra of the stalk module. -/
noncomputable def comparison : source F x ⟶ target F x :=
  ModuleCat.ofHom
    { toFun := addMap F x
      map_add' := addMap_add F x
      map_smul' := addMap_smul F x }

/-- The symmetric-algebra stalk comparison sends the germ of a degree-one generator to the
generator of the corresponding module germ. -/
theorem comparison_germ_ι (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    comparison F x
        (TopCat.Presheaf.germ
          (PresheafOfModules.SymmetricAlgebra.presheaf R F).presheaf U x hx
          (ModuleCat.symmetricAlgebra.ι
            (PresheafOfModules.SymmetricAlgebra.sectionObj R F (op U)) m)) =
      germGenerator F x U hx m := sorry

/-- The explicit inverse comparison obtained from the symmetric-algebra universal property. -/
@[stacks 01CH "inverse module-presheaf symmetric algebra stalk comparison"]
noncomputable def comparisonInv : target F x ⟶ source F x :=
  comparisonInvLift F x ≫ (sourceLinearIso F x).inv

/-- The forward symmetric-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "module-presheaf symmetric algebra stalk comparison on degree one"]
theorem comparison_ι :
    PresheafOfModules.stalkMapOfCommRing
        (PresheafOfModules.SymmetricAlgebra.ι R F) x ≫ comparison F x =
      ModuleCat.symmetricAlgebra.ιHom
        (PresheafOfModules.stalkModuleCatOfCommRing F x) := sorry

/-- The inverse symmetric-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "inverse module-presheaf symmetric algebra stalk comparison on degree one"]
theorem comparisonInv_ι :
    ModuleCat.symmetricAlgebra.ιHom
        (PresheafOfModules.stalkModuleCatOfCommRing F x) ≫ comparisonInv F x =
      PresheafOfModules.stalkMapOfCommRing
        (PresheafOfModules.SymmetricAlgebra.ι R F) x := sorry

/-- The inverse symmetric-algebra stalk comparison sends a generator of a germ to the germ of
the corresponding sectionwise generator. -/
@[simp, stacks 01CH "inverse symmetric algebra stalk comparison on germ generators"]
theorem comparisonInv_germGenerator (U : Opens X) (hx : x ∈ U)
    (m : F.obj (op U)) :
    comparisonInv F x (germGenerator F x U hx m) =
      TopCat.Presheaf.germ
        (PresheafOfModules.SymmetricAlgebra.presheaf R F).presheaf U x hx
        (ModuleCat.symmetricAlgebra.ι
          (PresheafOfModules.SymmetricAlgebra.sectionObj R F (op U)) m) := sorry

/-- The forward symmetric-algebra stalk comparison followed by its explicit inverse is the
identity. -/
@[simp, stacks 01CH "symmetric algebra stalk comparison component right inverse"]
theorem comparison_comp_comparisonInv :
    comparison F x ≫ comparisonInv F x = 𝟙 (source F x) := sorry

/-- The explicit inverse symmetric-algebra stalk comparison followed by the forward comparison
is the identity. -/
@[simp, stacks 01CH "symmetric algebra stalk comparison component left inverse"]
theorem comparisonInv_comp_comparison :
    comparisonInv F x ≫ comparison F x = 𝟙 (target F x) := sorry

/-- Stalks commute with sectionwise symmetric algebras of module presheaves. -/
instance comparison_isIso : IsIso (comparison F x) := sorry

/-- The canonical isomorphism from the stalk of the sectionwise symmetric algebra to the
symmetric algebra of the stalk module. -/
@[stacks 01CH "module-presheaf symmetric algebra stalk comparison isomorphism"]
noncomputable def comparisonIso : source F x ≅ target F x where
  hom := comparison F x
  inv := comparisonInv F x
  hom_inv_id := comparison_comp_comparisonInv F x
  inv_hom_id := comparisonInv_comp_comparison F x

/-- The forward map of `comparisonIso` is the explicit symmetric-algebra comparison. -/
@[simp, stacks 01CH "symmetric algebra stalk comparison isomorphism forward projection"]
theorem comparisonIso_hom : (comparisonIso F x).hom = comparison F x := sorry

/-- The inverse map of `comparisonIso` is the explicit symmetric-algebra universal lift. -/
@[simp, stacks 01CH "symmetric algebra stalk comparison isomorphism inverse projection"]
theorem comparisonIso_inv : (comparisonIso F x).inv = comparisonInv F x := sorry

/-- The explicit inverse symmetric-algebra stalk comparison is an isomorphism. -/
instance comparisonInv_isIso : IsIso (comparisonInv F x) := sorry

/-- The presheaf symmetric-algebra stalk comparison is natural in the module presheaf. -/
theorem comparison_naturality
    {F G : PresheafOfModules
      (CategoryTheory.Presheaf.ringPresheafOfComm R)} (f : F ⟶ G) (x : X) :
    CommSq
      (PresheafOfModules.stalkMapOfCommRing
        (PresheafOfModules.SymmetricAlgebra.hom R f) x)
      (comparison F x)
      (comparison G x)
      (ModuleCat.symmetricAlgebra.map
        (PresheafOfModules.stalkMapOfCommRing f x)) := sorry

/-- The explicit inverse symmetric-algebra stalk comparison is natural in the module
presheaf. -/
@[stacks 01CH "inverse module-presheaf symmetric algebra stalk comparison naturality"]
theorem comparisonInv_naturality
    {F G : PresheafOfModules
      (CategoryTheory.Presheaf.ringPresheafOfComm R)} (f : F ⟶ G) (x : X) :
    ModuleCat.symmetricAlgebra.map
        (PresheafOfModules.stalkMapOfCommRing f x) ≫ comparisonInv G x =
      comparisonInv F x ≫
        PresheafOfModules.stalkMapOfCommRing
          (PresheafOfModules.SymmetricAlgebra.hom R f) x := sorry

/-- The presheaf symmetric-algebra stalk isomorphism is natural in the module presheaf. -/
@[stacks 01CH "module-presheaf symmetric algebra stalk isomorphism naturality"]
theorem comparisonIso_naturality
    {F G : PresheafOfModules
      (CategoryTheory.Presheaf.ringPresheafOfComm R)} (f : F ⟶ G) (x : X) :
    (PresheafOfModules.SymmetricAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x).map f ≫
          (comparisonIso G x).hom =
      (comparisonIso F x).hom ≫
        (PresheafOfModules.stalkFunctorOfCommRing R x ⋙
          ModuleCat.symmetricAlgebra.functor (R.stalk x)).map f := sorry

/-- The symmetric-algebra stalk comparisons as a natural transformation. -/
@[stacks 01CH "module-presheaf symmetric algebra stalk natural transformation"]
noncomputable def natTrans (R : X.Presheaf CommRingCat.{u}) (x : X) :
    PresheafOfModules.SymmetricAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x ⟶
      PresheafOfModules.stalkFunctorOfCommRing R x ⋙
        ModuleCat.symmetricAlgebra.functor (R.stalk x) where
  app F := comparison F x
  naturality _ _ f := (comparison_naturality f x).w

/-- The explicit inverse symmetric-algebra stalk comparisons as a natural transformation. -/
@[stacks 01CH "inverse module-presheaf symmetric algebra stalk natural transformation"]
noncomputable def invNatTrans (R : X.Presheaf CommRingCat.{u}) (x : X) :
    PresheafOfModules.stalkFunctorOfCommRing R x ⋙
        ModuleCat.symmetricAlgebra.functor (R.stalk x) ⟶
      PresheafOfModules.SymmetricAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x where
  app F := comparisonInv F x
  naturality _ _ f := comparisonInv_naturality f x

/-- A component of the forward symmetric-algebra stalk natural transformation is the explicit
comparison. -/
@[simp, stacks 01CH "symmetric algebra stalk natural transformation component"]
theorem natTrans_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (natTrans R x).app F = comparison F x := sorry

/-- A component of the inverse symmetric-algebra stalk natural transformation is the explicit
universal-property inverse. -/
@[simp, stacks 01CH "inverse symmetric algebra stalk natural transformation component"]
theorem invNatTrans_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (invNatTrans R x).app F = comparisonInv F x := sorry

/-- The symmetric-algebra stalk natural transformation followed by its explicit inverse is the
identity natural transformation. -/
@[simp, stacks 01CH "symmetric algebra stalk natural transformation right inverse"]
theorem natTrans_comp_invNatTrans (R : X.Presheaf CommRingCat.{u}) (x : X) :
    natTrans R x ≫ invNatTrans R x =
      𝟙 (PresheafOfModules.SymmetricAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x) := sorry

/-- The explicit inverse symmetric-algebra stalk natural transformation followed by the
forward transformation is the identity. -/
@[simp, stacks 01CH "symmetric algebra stalk natural transformation left inverse"]
theorem invNatTrans_comp_natTrans (R : X.Presheaf CommRingCat.{u}) (x : X) :
    invNatTrans R x ≫ natTrans R x =
      𝟙 (PresheafOfModules.stalkFunctorOfCommRing R x ⋙
        ModuleCat.symmetricAlgebra.functor (R.stalk x)) := sorry

/-- The symmetric-algebra stalk comparison natural transformation is invertible. -/
@[stacks 01CH "module-presheaf symmetric algebra stalk natural transformation is invertible",
  instance]
instance natTrans_isIso (R : X.Presheaf CommRingCat.{u}) (x : X) :
    IsIso (natTrans R x) := sorry

/-- The symmetric-algebra stalk comparisons as a natural isomorphism. -/
@[stacks 01CH "module-presheaf symmetric algebra stalk natural isomorphism"]
noncomputable def comparisonNatIso (R : X.Presheaf CommRingCat.{u}) (x : X) :
    PresheafOfModules.SymmetricAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x ≅
      PresheafOfModules.stalkFunctorOfCommRing R x ⋙
        ModuleCat.symmetricAlgebra.functor (R.stalk x) where
  hom := natTrans R x
  inv := invNatTrans R x
  hom_inv_id := natTrans_comp_invNatTrans R x
  inv_hom_id := invNatTrans_comp_natTrans R x

/-- A component of `comparisonNatIso` is the pointwise symmetric-algebra comparison isomorphism. -/
@[simp, stacks 01CH "symmetric algebra stalk natural isomorphism component"]
theorem comparisonNatIso_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (comparisonNatIso R x).app F = comparisonIso F x := sorry

/-- The forward natural transformation of `comparisonNatIso` is `natTrans`. -/
@[simp, stacks 01CH "symmetric algebra stalk natural isomorphism forward projection"]
theorem comparisonNatIso_hom (R : X.Presheaf CommRingCat.{u}) (x : X) :
    (comparisonNatIso R x).hom = natTrans R x := sorry

/-- The inverse natural transformation of `comparisonNatIso` is the explicit universal-lift
comparison. -/
@[simp, stacks 01CH "symmetric algebra stalk natural isomorphism inverse projection"]
theorem comparisonNatIso_inv (R : X.Presheaf CommRingCat.{u}) (x : X) :
    (comparisonNatIso R x).inv = invNatTrans R x := sorry

/-- A forward component of `comparisonNatIso` is the explicit symmetric-algebra stalk
comparison. -/
@[simp, stacks 01CH "symmetric algebra stalk natural isomorphism forward component"]
theorem comparisonNatIso_hom_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (comparisonNatIso R x).hom.app F = comparison F x := sorry

/-- The inverse component of `comparisonNatIso` is the inverse pointwise comparison. -/
@[simp, stacks 01CH "symmetric algebra stalk natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (comparisonNatIso R x).inv.app F = comparisonInv F x := sorry

end PresheafOfModules.SymmetricAlgebra.Stalk

namespace PresheafOfModules.ExteriorAlgebra.Stalk

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
variable (F : PresheafOfModules
  (CategoryTheory.Presheaf.ringPresheafOfComm R)) (x : X)

/-- The stalk of the sectionwise exterior-algebra presheaf. -/
abbrev source : ModuleCat (R.stalk x) :=
  PresheafOfModules.stalkModuleCatOfCommRing
    (PresheafOfModules.ExteriorAlgebra.presheaf R F) x

/-- The exterior algebra of the stalk module. -/
abbrev target : ModuleCat (R.stalk x) :=
  (PresheafOfModules.stalkModuleCatOfCommRing F x).exteriorAlgebra

/-- The stalk of the ring-valued sectionwise exterior-algebra presheaf. -/
noncomputable abbrev sourceRing : RingCat.{u} :=
  TopCat.Presheaf.filteredStalk (C := RingCat.{u}) x
    (PresheafOfModules.ExteriorAlgebra.ringPresheaf R F)

/-- The structural ring map from the base stalk to the exterior-algebra ring stalk. -/
noncomputable abbrev sourceStructureMap : R.stalk x →+* sourceRing F x :=
  PresheafOfModules.AlgebraStalk.structureMap
    (PresheafOfModules.ExteriorAlgebra.ringPresheaf R F)
    (PresheafOfModules.ExteriorAlgebra.ringUnit R F) x

/-- The image of the base stalk is central in the exterior-algebra ring stalk. -/
theorem sourceStructureMap_commutes (r : R.stalk x) (a : sourceRing F x) :
    sourceStructureMap F x r * a = a * sourceStructureMap F x r := sorry

/-- The exterior-algebra ring stalk is canonically an algebra over the base stalk. -/
noncomputable instance sourceAlgebra : Algebra (R.stalk x) (sourceRing F x) :=
  RingHom.toAlgebra' (sourceStructureMap F x) (sourceStructureMap_commutes F x)

/-- The exterior-algebra ring stalk, regarded as a module over the base stalk. -/
noncomputable abbrev sourceModule : ModuleCat (R.stalk x) :=
  ModuleCat.of (R.stalk x) (sourceRing F x)

/-- The additive stalk of the module-valued exterior-algebra presheaf agrees with the
underlying additive group of the ring-valued stalk. -/
noncomputable def sourceAddIso :
    (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (source F x) ≅
      (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (sourceModule F x) :=
  PresheafOfModules.AlgebraStalk.sourceAddIso
    (PresheafOfModules.ExteriorAlgebra.ringPresheaf R F)
    (PresheafOfModules.ExteriorAlgebra.presheaf R F)
    (PresheafOfModules.ExteriorAlgebra.addCommGrpPresheafIso R F) x

/-- The additive exterior-algebra stalk comparison respects the base-stalk scalar action. -/
theorem sourceAddIso_smul (r : R.stalk x) :
    (sourceAddIso F x).hom ≫ (sourceModule F x).smul r =
      (source F x).smul r ≫ (sourceAddIso F x).hom := sorry

/-- The module-valued exterior-algebra stalk and the module underlying its ring stalk are
canonically isomorphic. -/
noncomputable def sourceLinearIso : source F x ≅ sourceModule F x :=
  ModuleCat.isoMk (sourceAddIso F x) (sourceAddIso_smul F x)

/-- The degree-one generator map from the stalk module into the exterior-algebra ring stalk. -/
noncomputable def stalkGenerator :
    PresheafOfModules.stalkModuleCatOfCommRing F x ⟶ sourceModule F x :=
  PresheafOfModules.stalkMapOfCommRing
      (PresheafOfModules.ExteriorAlgebra.ι R F) x ≫
    (sourceLinearIso F x).hom

/-- Every element in the image of the exterior-algebra stalk generator squares to zero. -/
theorem stalkGenerator_sq_zero
    (m : PresheafOfModules.stalkModuleCatOfCommRing F x) :
    stalkGenerator F x m * stalkGenerator F x m = 0 := sorry

/-- The universal exterior-algebra lift into the ring-valued exterior-algebra stalk. -/
noncomputable def comparisonInvLift : target F x ⟶ sourceModule F x :=
  ModuleCat.ofHom
    (_root_.ExteriorAlgebra.lift (R.stalk x)
      ⟨(stalkGenerator F x).hom, stalkGenerator_sq_zero F x⟩).toLinearMap

/-- The degree-one exterior-algebra generator determined by the germ of a section. -/
def germGenerator (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) : target F x :=
  ModuleCat.exteriorAlgebra.ι (PresheafOfModules.stalkModuleCatOfCommRing F x)
    (TopCat.Presheaf.germ F.presheaf U x hx m)

/-- The neighborhood leg from a sectionwise exterior algebra to the exterior algebra of the
stalk module. -/
noncomputable def leg (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙
      (PresheafOfModules.ExteriorAlgebra.presheaf R F).presheaf).obj U) ⟶
      (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target F x) :=
  AddCommGrpCat.ofHom
    (ModuleCat.exteriorAlgebra.mapRestrictScalars
      (R.germ U.unop.1 x U.unop.2).hom
      (PresheafOfModules.germToStalk F x U.unop.1 U.unop.2)).hom.toAddMonoidHom

/-- An exterior-algebra neighborhood leg sends a degree-one generator to the generator of its
germ. -/
theorem leg_ι (U : (OpenNhds x)ᵒᵖ)
    (m : F.obj ((OpenNhds.inclusion x).op.obj U)) :
    leg F x U
        (ModuleCat.exteriorAlgebra.ι
          (PresheafOfModules.ExteriorAlgebra.sectionObj R F
            ((OpenNhds.inclusion x).op.obj U)) m) =
      germGenerator F x U.unop.1 U.unop.2 m := sorry

/-- The exterior-algebra neighborhood legs are compatible with restriction. -/
theorem leg_naturality {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙
      (PresheafOfModules.ExteriorAlgebra.presheaf R F).presheaf).map i) ≫
        leg F x V =
      leg F x U := sorry

/-- The cocone of neighborhood exterior algebras with vertex the exterior algebra of the stalk
module. -/
noncomputable def cocone :
    Cocone ((OpenNhds.inclusion x).op ⋙
      (PresheafOfModules.ExteriorAlgebra.presheaf R F).presheaf) where
  pt := (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target F x)
  ι :=
    { app := leg F x
      naturality := fun _ _ i ↦ leg_naturality F x i }

/-- The additive map from the stalk of the sectionwise exterior algebra to the exterior algebra
of the stalk module. -/
noncomputable def addMap :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (PresheafOfModules.ExteriorAlgebra.presheaf R F).presheaf x ⟶
      (forget₂ (ModuleCat (R.stalk x)) AddCommGrpCat.{u}).obj (target F x) :=
  colimit.desc _ (cocone F x)

/-- The additive exterior-algebra stalk map preserves addition. -/
theorem addMap_add (m n : source F x) :
    addMap F x (m + n) = addMap F x m + addMap F x n := sorry

/-- The additive exterior-algebra stalk map is linear over the stalk ring. -/
theorem addMap_smul (r : R.stalk x) (m : source F x) :
    addMap F x (r • m) =
      HSMul.hSMul (α := R.stalk x) (β := target F x) r (addMap F x m) := sorry

/-- The canonical comparison from the stalk of the sectionwise exterior algebra to the exterior
algebra of the stalk module. -/
noncomputable def comparison : source F x ⟶ target F x :=
  ModuleCat.ofHom
    { toFun := addMap F x
      map_add' := addMap_add F x
      map_smul' := addMap_smul F x }

/-- The exterior-algebra stalk comparison sends the germ of a degree-one generator to the
generator of the corresponding module germ. -/
theorem comparison_germ_ι (U : Opens X) (hx : x ∈ U) (m : F.obj (op U)) :
    comparison F x
        (TopCat.Presheaf.germ
          (PresheafOfModules.ExteriorAlgebra.presheaf R F).presheaf U x hx
          (ModuleCat.exteriorAlgebra.ι
            (PresheafOfModules.ExteriorAlgebra.sectionObj R F (op U)) m)) =
      germGenerator F x U hx m := sorry

/-- The explicit inverse comparison obtained from the exterior-algebra universal property. -/
@[stacks 01CH "inverse module-presheaf exterior algebra stalk comparison"]
noncomputable def comparisonInv : target F x ⟶ source F x :=
  comparisonInvLift F x ≫ (sourceLinearIso F x).inv

/-- The forward exterior-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "module-presheaf exterior algebra stalk comparison on degree one"]
theorem comparison_ι :
    PresheafOfModules.stalkMapOfCommRing
        (PresheafOfModules.ExteriorAlgebra.ι R F) x ≫ comparison F x =
      ModuleCat.exteriorAlgebra.ιHom
        (PresheafOfModules.stalkModuleCatOfCommRing F x) := sorry

/-- The inverse exterior-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "inverse module-presheaf exterior algebra stalk comparison on degree one"]
theorem comparisonInv_ι :
    ModuleCat.exteriorAlgebra.ιHom
        (PresheafOfModules.stalkModuleCatOfCommRing F x) ≫ comparisonInv F x =
      PresheafOfModules.stalkMapOfCommRing
        (PresheafOfModules.ExteriorAlgebra.ι R F) x := sorry

/-- The inverse exterior-algebra stalk comparison sends a generator of a germ to the germ of
the corresponding sectionwise generator. -/
@[simp, stacks 01CH "inverse exterior algebra stalk comparison on germ generators"]
theorem comparisonInv_germGenerator (U : Opens X) (hx : x ∈ U)
    (m : F.obj (op U)) :
    comparisonInv F x (germGenerator F x U hx m) =
      TopCat.Presheaf.germ
        (PresheafOfModules.ExteriorAlgebra.presheaf R F).presheaf U x hx
        (ModuleCat.exteriorAlgebra.ι
          (PresheafOfModules.ExteriorAlgebra.sectionObj R F (op U)) m) := sorry

/-- The forward exterior-algebra stalk comparison followed by its explicit inverse is the
identity. -/
@[simp, stacks 01CH "exterior algebra stalk comparison component right inverse"]
theorem comparison_comp_comparisonInv :
    comparison F x ≫ comparisonInv F x = 𝟙 (source F x) := sorry

/-- The explicit inverse exterior-algebra stalk comparison followed by the forward comparison
is the identity. -/
@[simp, stacks 01CH "exterior algebra stalk comparison component left inverse"]
theorem comparisonInv_comp_comparison :
    comparisonInv F x ≫ comparison F x = 𝟙 (target F x) := sorry

/-- Stalks commute with sectionwise exterior algebras of module presheaves. -/
instance comparison_isIso : IsIso (comparison F x) := sorry

/-- The canonical isomorphism from the stalk of the sectionwise exterior algebra to the exterior
algebra of the stalk module. -/
@[stacks 01CH "module-presheaf exterior algebra stalk comparison isomorphism"]
noncomputable def comparisonIso : source F x ≅ target F x where
  hom := comparison F x
  inv := comparisonInv F x
  hom_inv_id := comparison_comp_comparisonInv F x
  inv_hom_id := comparisonInv_comp_comparison F x

/-- The forward map of `comparisonIso` is the explicit exterior-algebra comparison. -/
@[simp, stacks 01CH "exterior algebra stalk comparison isomorphism forward projection"]
theorem comparisonIso_hom : (comparisonIso F x).hom = comparison F x := sorry

/-- The inverse map of `comparisonIso` is the explicit exterior-algebra universal lift. -/
@[simp, stacks 01CH "exterior algebra stalk comparison isomorphism inverse projection"]
theorem comparisonIso_inv : (comparisonIso F x).inv = comparisonInv F x := sorry

/-- The explicit inverse exterior-algebra stalk comparison is an isomorphism. -/
instance comparisonInv_isIso : IsIso (comparisonInv F x) := sorry

/-- The presheaf exterior-algebra stalk comparison is natural in the module presheaf. -/
theorem comparison_naturality
    {F G : PresheafOfModules
      (CategoryTheory.Presheaf.ringPresheafOfComm R)} (f : F ⟶ G) (x : X) :
    CommSq
      (PresheafOfModules.stalkMapOfCommRing
        (PresheafOfModules.ExteriorAlgebra.hom R f) x)
      (comparison F x)
      (comparison G x)
      (ModuleCat.exteriorAlgebra.map
        (PresheafOfModules.stalkMapOfCommRing f x)) := sorry

/-- The explicit inverse exterior-algebra stalk comparison is natural in the module
presheaf. -/
@[stacks 01CH "inverse module-presheaf exterior algebra stalk comparison naturality"]
theorem comparisonInv_naturality
    {F G : PresheafOfModules
      (CategoryTheory.Presheaf.ringPresheafOfComm R)} (f : F ⟶ G) (x : X) :
    ModuleCat.exteriorAlgebra.map
        (PresheafOfModules.stalkMapOfCommRing f x) ≫ comparisonInv G x =
      comparisonInv F x ≫
        PresheafOfModules.stalkMapOfCommRing
          (PresheafOfModules.ExteriorAlgebra.hom R f) x := sorry

/-- The presheaf exterior-algebra stalk isomorphism is natural in the module presheaf. -/
@[stacks 01CH "module-presheaf exterior algebra stalk isomorphism naturality"]
theorem comparisonIso_naturality
    {F G : PresheafOfModules
      (CategoryTheory.Presheaf.ringPresheafOfComm R)} (f : F ⟶ G) (x : X) :
    (PresheafOfModules.ExteriorAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x).map f ≫
          (comparisonIso G x).hom =
      (comparisonIso F x).hom ≫
        (PresheafOfModules.stalkFunctorOfCommRing R x ⋙
          ModuleCat.exteriorAlgebra.functor (R.stalk x)).map f := sorry

/-- The exterior-algebra stalk comparisons as a natural transformation. -/
@[stacks 01CH "module-presheaf exterior algebra stalk natural transformation"]
noncomputable def natTrans (R : X.Presheaf CommRingCat.{u}) (x : X) :
    PresheafOfModules.ExteriorAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x ⟶
      PresheafOfModules.stalkFunctorOfCommRing R x ⋙
        ModuleCat.exteriorAlgebra.functor (R.stalk x) where
  app F := comparison F x
  naturality _ _ f := (comparison_naturality f x).w

/-- The explicit inverse exterior-algebra stalk comparisons as a natural transformation. -/
@[stacks 01CH "inverse module-presheaf exterior algebra stalk natural transformation"]
noncomputable def invNatTrans (R : X.Presheaf CommRingCat.{u}) (x : X) :
    PresheafOfModules.stalkFunctorOfCommRing R x ⋙
        ModuleCat.exteriorAlgebra.functor (R.stalk x) ⟶
      PresheafOfModules.ExteriorAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x where
  app F := comparisonInv F x
  naturality _ _ f := comparisonInv_naturality f x

/-- A component of the forward exterior-algebra stalk natural transformation is the explicit
comparison. -/
@[simp, stacks 01CH "exterior algebra stalk natural transformation component"]
theorem natTrans_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (natTrans R x).app F = comparison F x := sorry

/-- A component of the inverse exterior-algebra stalk natural transformation is the explicit
universal-property inverse. -/
@[simp, stacks 01CH "inverse exterior algebra stalk natural transformation component"]
theorem invNatTrans_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (invNatTrans R x).app F = comparisonInv F x := sorry

/-- The exterior-algebra stalk natural transformation followed by its explicit inverse is the
identity natural transformation. -/
@[simp, stacks 01CH "exterior algebra stalk natural transformation right inverse"]
theorem natTrans_comp_invNatTrans (R : X.Presheaf CommRingCat.{u}) (x : X) :
    natTrans R x ≫ invNatTrans R x =
      𝟙 (PresheafOfModules.ExteriorAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x) := sorry

/-- The explicit inverse exterior-algebra stalk natural transformation followed by the forward
transformation is the identity. -/
@[simp, stacks 01CH "exterior algebra stalk natural transformation left inverse"]
theorem invNatTrans_comp_natTrans (R : X.Presheaf CommRingCat.{u}) (x : X) :
    invNatTrans R x ≫ natTrans R x =
      𝟙 (PresheafOfModules.stalkFunctorOfCommRing R x ⋙
        ModuleCat.exteriorAlgebra.functor (R.stalk x)) := sorry

/-- The exterior-algebra stalk comparison natural transformation is invertible. -/
@[stacks 01CH "module-presheaf exterior algebra stalk natural transformation is invertible",
  instance]
instance natTrans_isIso (R : X.Presheaf CommRingCat.{u}) (x : X) :
    IsIso (natTrans R x) := sorry

/-- The exterior-algebra stalk comparisons as a natural isomorphism. -/
@[stacks 01CH "module-presheaf exterior algebra stalk natural isomorphism"]
noncomputable def comparisonNatIso (R : X.Presheaf CommRingCat.{u}) (x : X) :
    PresheafOfModules.ExteriorAlgebra.functor R ⋙
        PresheafOfModules.stalkFunctorOfCommRing R x ≅
      PresheafOfModules.stalkFunctorOfCommRing R x ⋙
        ModuleCat.exteriorAlgebra.functor (R.stalk x) where
  hom := natTrans R x
  inv := invNatTrans R x
  hom_inv_id := natTrans_comp_invNatTrans R x
  inv_hom_id := invNatTrans_comp_natTrans R x

/-- A component of `comparisonNatIso` is the pointwise exterior-algebra comparison isomorphism. -/
@[simp, stacks 01CH "exterior algebra stalk natural isomorphism component"]
theorem comparisonNatIso_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (comparisonNatIso R x).app F = comparisonIso F x := sorry

/-- The forward natural transformation of `comparisonNatIso` is `natTrans`. -/
@[simp, stacks 01CH "exterior algebra stalk natural isomorphism forward projection"]
theorem comparisonNatIso_hom (R : X.Presheaf CommRingCat.{u}) (x : X) :
    (comparisonNatIso R x).hom = natTrans R x := sorry

/-- The inverse natural transformation of `comparisonNatIso` is the explicit universal-lift
comparison. -/
@[simp, stacks 01CH "exterior algebra stalk natural isomorphism inverse projection"]
theorem comparisonNatIso_inv (R : X.Presheaf CommRingCat.{u}) (x : X) :
    (comparisonNatIso R x).inv = invNatTrans R x := sorry

/-- A forward component of `comparisonNatIso` is the explicit exterior-algebra stalk
comparison. -/
@[simp, stacks 01CH "exterior algebra stalk natural isomorphism forward component"]
theorem comparisonNatIso_hom_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (comparisonNatIso R x).hom.app F = comparison F x := sorry

/-- The inverse component of `comparisonNatIso` is the inverse pointwise comparison. -/
@[simp, stacks 01CH "exterior algebra stalk natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app (R : X.Presheaf CommRingCat.{u}) (x : X)
    (F : PresheafOfModules (CategoryTheory.Presheaf.ringPresheafOfComm R)) :
    (comparisonNatIso R x).inv.app F = comparisonInv F x := sorry

end PresheafOfModules.ExteriorAlgebra.Stalk
