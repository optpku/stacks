/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.AlgebraStalk
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Exterior
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Symmetric
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebra sheaves and stalks on ringed spaces

The topology-independent algebra-stalk comparisons are owned by
`ReasLib.Algebra.Category.ModuleCat.Presheaf.AlgebraStalk`.  This file only transports them
across module sheafification to the tensor, symmetric, and exterior algebra sheaves on a
ringed space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open SheafOfModules.RingedSite

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Forgetting module structure identifies the inverse sheafification counit with the
additive sheafification unit. -/
private theorem algebraSheafificationValIso_inv_toPresheaf (F : X.Modules) :
    (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (moduleSheafificationValIso X.sheaf F).inv =
      CategoryTheory.toSheafify (Opens.grothendieckTopology X) F.val.presheaf := by
  let adj := moduleSheafificationAdjunction X.sheaf
  let e := moduleSheafificationValIso X.sheaf F
  let U := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.toPresheaf X.ringCatSheaf.obj
  have h : adj.homEquiv F.val F e.hom = (valRestrictionIso X.sheaf F).hom := by
    apply (adj.homEquiv F.val F).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    rfl
  have h' : CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      F.val.presheaf ≫ U.map e.hom = 𝟙 F.val.presheaf := by
    have hh := congrArg (fun k ↦ (PresheafOfModules.toPresheaf
      X.ringCatSheaf.obj).map k) h
    change CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      F.val.presheaf ≫ U.map e.hom = 𝟙 F.val.presheaf at hh
    exact hh
  apply (cancel_mono (U.map e.hom)).1
  change U.map e.inv ≫ U.map e.hom =
    CategoryTheory.toSheafify (Opens.grothendieckTopology X) F.val.presheaf ≫ U.map e.hom
  rw [← U.map_comp, e.inv_hom_id, U.map_id, h']
  rfl

/-- The lift of a map out of a module sheaf agrees with the sheafification unit on sections. -/
private theorem algebraSheafification_lift_toPresheaf (F : X.Modules)
    (P : X.PresheafModules) (f : F.val ⟶ P) :
    (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        ((moduleSheafificationValIso X.sheaf F).inv ≫
          (_root_.moduleSheafification X.sheaf).map f) =
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f ≫
        CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf := by
  rw [Functor.map_comp, algebraSheafificationValIso_inv_toPresheaf]
  exact (CategoryTheory.toSheafify_naturality
    (J := Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f)).symm

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.RingedSpace.TensorAlg.Stalk

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The stalk of the tensor-algebra sheaf. -/
abbrev source (F : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  RingedSpace.stalkModuleCat (TensorAlg.sheaf F) x

/-- The tensor algebra of the stalk of a module sheaf. -/
abbrev target (F : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  (RingedSpace.stalkModuleCat F x).tensorAlgebra

/-- The canonical identification of the stalk of the sectionwise tensor-algebra presheaf with
the stalk of its module sheafification. -/
noncomputable abbrev sheafificationIso (F : X.Modules) (x : X) :=
  TopCat.Sheaf.moduleSheafificationStalkIso X.sheaf (TensorAlg.presheaf F) x

/-- Lemma 17.21.2 (01CH), tensor case: the canonical forward comparison from the stalk of the
tensor-algebra sheaf to the tensor algebra of the stalk module. -/
@[stacks 01CH "tensor algebra stalk comparison"]
noncomputable def comparison (F : X.Modules) (x : X) : source F x ⟶ target F x :=
  (sheafificationIso F x).inv ≫
    PresheafOfModules.TensorAlgebra.Stalk.comparison (R := X.presheaf) F.val x

/-- The explicit inverse tensor-algebra stalk comparison, transported through
sheafification. -/
@[stacks 01CH "inverse tensor algebra stalk comparison"]
noncomputable def comparisonInv (F : X.Modules) (x : X) : target F x ⟶ source F x :=
  PresheafOfModules.TensorAlgebra.Stalk.comparisonInv
      (R := X.presheaf) F.val x ≫
    (sheafificationIso F x).hom

/-- The tensor-algebra stalk comparison followed by its explicit inverse is the identity. -/
@[simp]
theorem comparison_comp_comparisonInv (F : X.Modules) (x : X) :
    comparison F x ≫ comparisonInv F x = 𝟙 (source F x) := by
  exact ((sheafificationIso F x).symm ≪≫
    PresheafOfModules.TensorAlgebra.Stalk.comparisonIso (R := X.presheaf) F.val x).hom_inv_id

/-- The explicit inverse tensor-algebra stalk comparison followed by the forward comparison is
the identity. -/
@[simp]
theorem comparisonInv_comp_comparison (F : X.Modules) (x : X) :
    comparisonInv F x ≫ comparison F x = 𝟙 (target F x) := by
  exact ((sheafificationIso F x).symm ≪≫
    PresheafOfModules.TensorAlgebra.Stalk.comparisonIso (R := X.presheaf) F.val x).inv_hom_id

/-- Lemma 17.21.2 (01CH), tensor case: the tensor-algebra stalk comparison is an
isomorphism. -/
@[stacks 01CH "tensor algebra stalk comparison is an isomorphism", instance]
instance comparison_isIso (F : X.Modules) (x : X) : IsIso (comparison F x) := by
  exact ⟨⟨comparisonInv F x, comparison_comp_comparisonInv F x,
    comparisonInv_comp_comparison F x⟩⟩

/-- The explicit isomorphism-valued form is the preferred downstream API. -/
@[stacks 01CH "tensor algebra stalk comparison isomorphism"]
noncomputable def comparisonIso (F : X.Modules) (x : X) :
    source F x ≅ target F x :=
  (sheafificationIso F x).symm ≪≫
    PresheafOfModules.TensorAlgebra.Stalk.comparisonIso
      (R := X.presheaf) F.val x

/-- The forward map of `comparisonIso` is the canonical comparison morphism. -/
@[simp]
theorem comparisonIso_hom (F : X.Modules) (x : X) :
    (comparisonIso F x).hom = comparison F x := by
  rfl

/-- The inverse map of `comparisonIso` is the transported universal-lift comparison. -/
@[simp]
theorem comparisonIso_inv (F : X.Modules) (x : X) :
    (comparisonIso F x).inv = comparisonInv F x := by
  rfl

/-- The explicit inverse tensor-algebra stalk comparison is an isomorphism. -/
instance comparisonInv_isIso (F : X.Modules) (x : X) :
    IsIso (comparisonInv F x) := by
  exact ⟨⟨comparison F x, comparisonInv_comp_comparison F x,
    comparison_comp_comparisonInv F x⟩⟩

/-- The tensor-algebra stalk comparison sends the germ of a local degree-one generator to the
degree-one generator of the corresponding module germ. -/
@[stacks 01CH "tensor algebra stalk comparison on germs of degree-one generators"]
theorem comparison_germ_ι (F : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    comparison F x
        (TopCat.Presheaf.germ (TensorAlg.sheaf F).val.presheaf U x hx
          ((TensorAlg.ι F).val.app (op U) m)) =
      ModuleCat.tensorAlgebra.ι (RingedSpace.stalkModuleCat F x)
        (TopCat.Presheaf.germ F.val.presheaf U x hx m) := by
  have hι := congrArg
    (fun k : F.val.presheaf ⟶ (TensorAlg.sheaf F).val.presheaf ↦ k.app (op U) m)
    (algebraSheafification_lift_toPresheaf F (TensorAlg.presheaf F) (TensorAlg.presheafι F))
  change (TensorAlg.ι F).val.app (op U) m =
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app (TensorAlg.presheaf F)).app (op U)
        ((TensorAlg.presheafι F).app (op U) m) at hι
  change PresheafOfModules.TensorAlgebra.Stalk.comparison (R := X.presheaf) F.val x
    (TopCat.Sheaf.moduleSheafificationStalkComparisonInv X.sheaf (TensorAlg.presheaf F) x
      (TopCat.Presheaf.germ (TensorAlg.sheaf F).val.presheaf U x hx
        ((TensorAlg.ι F).val.app (op U) m))) = _
  rw [hι]
  have hs := TopCat.Sheaf.moduleSheafificationStalkComparisonInv_germ
    X.sheaf (TensorAlg.presheaf F) x U hx ((TensorAlg.presheafι F).app (op U) m)
  exact (congrArg (PresheafOfModules.TensorAlgebra.Stalk.comparison (R := X.presheaf) F.val x) hs).trans
    (PresheafOfModules.TensorAlgebra.Stalk.comparison_germ_ι (R := X.presheaf) F.val x U hx m)

/-- The inverse tensor-algebra stalk comparison sends a degree-one generator of a module germ
to the germ of the corresponding sheaf generator. -/
@[stacks 01CH "inverse tensor algebra stalk comparison on germ generators"]
theorem comparisonInv_germ_ι (F : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    comparisonInv F x
        (ModuleCat.tensorAlgebra.ι (RingedSpace.stalkModuleCat F x)
          (TopCat.Presheaf.germ F.val.presheaf U x hx m)) =
      TopCat.Presheaf.germ (TensorAlg.sheaf F).val.presheaf U x hx
        ((TensorAlg.ι F).val.app (op U) m) := by
  rw [← comparison_germ_ι F x U hx m]
  change (comparison F x ≫ comparisonInv F x)
    (TopCat.Presheaf.germ (TensorAlg.sheaf F).val.presheaf U x hx
      ((TensorAlg.ι F).val.app (op U) m)) = _
  rw [comparison_comp_comparisonInv]
  rfl

/-- The tensor-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "tensor algebra stalk comparison preserves degree-one inclusion"]
theorem comparison_ι (F : X.Modules) (x : X) :
    RingedSpace.moduleStalkHom x (TensorAlg.ι F) ≫ comparison F x =
      ModuleCat.tensorAlgebra.ιHom (RingedSpace.stalkModuleCat F x) := by
  ext m
  obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
  change comparison F x
    ((RingedSpace.moduleStalkHom x (TensorAlg.ι F)).hom
      (TopCat.Presheaf.germ F.val.presheaf U x hx s)) = _
  have hg : ((RingedSpace.moduleStalkHom x (TensorAlg.ι F)).hom
      (TopCat.Presheaf.germ F.val.presheaf U x hx s)) =
      TopCat.Presheaf.germ (TensorAlg.sheaf F).val.presheaf U x hx
        ((TensorAlg.ι F).val.app (op U) s) :=
    SheafOfModules.stalkFunctorOfCommRing_map_germ
      (𝒪 := X.sheaf) (TensorAlg.ι F) U x hx s
  rw [hg]
  exact comparison_germ_ι F x U hx s

/-- The inverse tensor-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "inverse tensor algebra stalk comparison preserves degree one"]
theorem comparisonInv_ι (F : X.Modules) (x : X) :
    ModuleCat.tensorAlgebra.ιHom (RingedSpace.stalkModuleCat F x) ≫
        comparisonInv F x =
      RingedSpace.moduleStalkHom x (TensorAlg.ι F) := by
  apply (cancel_mono (comparison F x)).1
  rw [Category.assoc, comparisonInv_comp_comparison, Category.comp_id, comparison_ι]

/-- The tensor-algebra stalk comparison preserves the multiplicative unit. -/
@[reassoc, stacks 01CH "tensor algebra stalk comparison preserves the unit"]
theorem comparison_one (F : X.Modules) (x : X) :
    RingedSpace.moduleStalkHom x (TensorAlg.one F) ≫ comparison F x =
      RingedSpace.moduleStalkHom x (RingedSpace.unitIsoTensorUnit X).inv ≫
        RingedSpace.unitStalkLinearMap x ≫
          ModuleCat.tensorAlgebra.one (RingedSpace.stalkModuleCat F x) := sorry

/-- The tensor-algebra stalk comparison preserves multiplication. -/
@[reassoc, stacks 01CH "tensor algebra stalk comparison preserves multiplication"]
theorem comparison_mul (F : X.Modules) (x : X) :
    RingedSpace.moduleStalkHom x (TensorAlg.mul F) ≫ comparison F x =
      RingedSpace.Tensor.Stalk.comparison (TensorAlg.sheaf F) (TensorAlg.sheaf F) x ≫
        tensorHom (comparison F x) (comparison F x) ≫
          ModuleCat.tensorAlgebra.mul (RingedSpace.stalkModuleCat F x) := sorry

/-- The tensor-algebra stalk comparison is natural in the module sheaf. -/
@[stacks 01CH "tensor algebra stalk comparison naturality"]
theorem comparison_naturality {F G : X.Modules} (f : F ⟶ G) (x : X) :
    CommSq
      (RingedSpace.moduleStalkHom x (TensorAlg.map f))
      (comparison F x)
      (comparison G x)
      (ModuleCat.tensorAlgebra.map (RingedSpace.moduleStalkHom x f)) := by
  constructor
  change RingedSpace.moduleStalkHom x (TensorAlg.map f) ≫
      ((sheafificationIso G x).inv ≫
        PresheafOfModules.TensorAlgebra.Stalk.comparison (R := X.presheaf) G.val x) =
    ((sheafificationIso F x).inv ≫
      PresheafOfModules.TensorAlgebra.Stalk.comparison (R := X.presheaf) F.val x) ≫
        ModuleCat.tensorAlgebra.map (RingedSpace.moduleStalkHom x f)
  have h : RingedSpace.moduleStalkHom x (TensorAlg.map f) ≫
      (sheafificationIso G x).inv =
      (sheafificationIso F x).inv ≫
        PresheafOfModules.stalkMapOfCommRing
          (PresheafOfModules.TensorAlgebra.hom X.presheaf f.val) x :=
    TopCat.Sheaf.moduleSheafificationStalkComparisonInv_naturality
      X.sheaf (PresheafOfModules.TensorAlgebra.hom X.presheaf f.val) x
  have h' : PresheafOfModules.stalkMapOfCommRing
      (PresheafOfModules.TensorAlgebra.hom X.presheaf f.val) x ≫
        PresheafOfModules.TensorAlgebra.Stalk.comparison (R := X.presheaf) G.val x =
      PresheafOfModules.TensorAlgebra.Stalk.comparison (R := X.presheaf) F.val x ≫
        ModuleCat.tensorAlgebra.map (RingedSpace.moduleStalkHom x f) :=
    (PresheafOfModules.TensorAlgebra.Stalk.comparison_naturality (R := X.presheaf) f.val x).w
  rw [← Category.assoc, h]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ (sheafificationIso F x).inv ≫ k) h').trans
      (Category.assoc _ _ _).symm)

/-- The explicit inverse tensor-algebra stalk comparison is natural in the module sheaf. -/
@[stacks 01CH "inverse tensor algebra stalk comparison naturality"]
theorem comparisonInv_naturality {F G : X.Modules} (f : F ⟶ G) (x : X) :
    ModuleCat.tensorAlgebra.map (RingedSpace.moduleStalkHom x f) ≫
        comparisonInv G x =
      comparisonInv F x ≫ RingedSpace.moduleStalkHom x (TensorAlg.map f) := by
  apply (cancel_mono (comparison G x)).1
  simp only [Category.assoc, comparisonInv_comp_comparison, Category.comp_id]
  rw [(comparison_naturality f x).w, ← Category.assoc,
    comparisonInv_comp_comparison, Category.id_comp]

/-- Lemma 17.21.2 (01CH), tensor case: the stalk comparisons assemble into a natural
transformation in the module sheaf. -/
@[stacks 01CH "tensor algebra stalk natural transformation"]
noncomputable def natTrans (x : X) :
    TensorAlg.functor X ⋙ X.stalkModuleFunctor x ⟶
      X.stalkModuleFunctor x ⋙ ModuleCat.tensorAlgebra.functor (X.presheaf.stalk x) :=
  { app := fun F ↦ comparison F x
    naturality := fun {F G} f ↦ (comparison_naturality (F := F) (G := G) f x).w }

/-- The explicit inverse tensor-algebra stalk comparisons form a natural transformation. -/
@[stacks 01CH "inverse tensor algebra stalk natural transformation"]
noncomputable def invNatTrans (x : X) :
    X.stalkModuleFunctor x ⋙ ModuleCat.tensorAlgebra.functor (X.presheaf.stalk x) ⟶
      TensorAlg.functor X ⋙ X.stalkModuleFunctor x where
  app F := comparisonInv F x
  naturality _ _ f := comparisonInv_naturality f x

/-- Lemma 17.21.2 (01CH), tensor case: the tensor-algebra stalk natural transformation is
invertible. -/
@[stacks 01CH "tensor algebra stalk natural transformation is invertible", instance]
instance natTrans_isIso (x : X) : IsIso (natTrans x) := by
  exact ⟨⟨invNatTrans x,
    NatTrans.ext (funext fun F ↦ comparison_comp_comparisonInv F x),
    NatTrans.ext (funext fun F ↦ comparisonInv_comp_comparison F x)⟩⟩

/-- The tensor-algebra stalk isomorphism is natural in the module sheaf. -/
@[stacks 01CH "tensor algebra stalk comparison isomorphism naturality"]
theorem comparisonIso_naturality (x : X) {F G : X.Modules} (f : F ⟶ G) :
    (TensorAlg.functor X ⋙ X.stalkModuleFunctor x).map f ≫
        (comparisonIso G x).hom =
      (comparisonIso F x).hom ≫
        (X.stalkModuleFunctor x ⋙
          ModuleCat.tensorAlgebra.functor (X.presheaf.stalk x)).map f := by
  change RingedSpace.moduleStalkHom x (TensorAlg.map f) ≫ comparison G x =
    comparison F x ≫ ModuleCat.tensorAlgebra.map (RingedSpace.moduleStalkHom x f)
  exact (comparison_naturality f x).w

/-- The tensor-algebra stalk comparison natural transformation followed by its explicit inverse
is the identity. -/
@[simp, stacks 01CH "tensor algebra stalk natural forward-inverse law"]
theorem natTrans_hom_inv_id (x : X) :
    natTrans x ≫ invNatTrans x = 𝟙 _ := by
  apply NatTrans.ext
  funext F
  exact comparison_comp_comparisonInv F x

/-- The explicit inverse tensor-algebra stalk natural transformation followed by the comparison
is the identity. -/
@[simp, stacks 01CH "tensor algebra stalk natural inverse-forward law"]
theorem natTrans_inv_hom_id (x : X) :
    invNatTrans x ≫ natTrans x = 𝟙 _ := by
  apply NatTrans.ext
  funext F
  exact comparisonInv_comp_comparison F x

/-- The tensor-algebra stalk comparisons form a natural isomorphism. -/
@[stacks 01CH "tensor algebra stalk comparison natural isomorphism"]
noncomputable def comparisonNatIso (x : X) :
    TensorAlg.functor X ⋙ X.stalkModuleFunctor x ≅
      X.stalkModuleFunctor x ⋙
        ModuleCat.tensorAlgebra.functor (X.presheaf.stalk x) where
  hom := natTrans x
  inv := invNatTrans x
  hom_inv_id := natTrans_hom_inv_id x
  inv_hom_id := natTrans_inv_hom_id x

/-- A component of `comparisonNatIso` is the pointwise tensor-algebra comparison isomorphism. -/
@[simp, stacks 01CH "tensor algebra stalk natural isomorphism component"]
theorem comparisonNatIso_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).app F = comparisonIso F x := by
  apply Iso.ext
  rfl

/-- The forward natural transformation of `comparisonNatIso` is `natTrans`. -/
@[simp, stacks 01CH "tensor algebra stalk natural isomorphism hom"]
theorem comparisonNatIso_hom (x : X) :
    (comparisonNatIso x).hom = natTrans x := by
  rfl

/-- The inverse natural transformation of `comparisonNatIso` is the explicit transported
universal-lift comparison. -/
@[simp, stacks 01CH "tensor algebra stalk natural isomorphism inverse"]
theorem comparisonNatIso_inv (x : X) :
    (comparisonNatIso x).inv = invNatTrans x := by
  rfl

/-- The forward component of `comparisonNatIso` is the canonical comparison morphism. -/
@[simp, stacks 01CH "tensor algebra stalk natural isomorphism hom component"]
theorem comparisonNatIso_hom_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).hom.app F = comparison F x := by
  rfl

/-- The inverse component of `comparisonNatIso` is the inverse pointwise comparison. -/
@[simp, stacks 01CH "tensor algebra stalk natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).inv.app F = comparisonInv F x := by
  rfl

end AlgebraicGeometry.RingedSpace.TensorAlg.Stalk

namespace AlgebraicGeometry.RingedSpace.SymmetricAlg.Stalk

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The stalk of the symmetric-algebra sheaf. -/
abbrev source (F : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  RingedSpace.stalkModuleCat (SymmetricAlg.sheaf F) x

/-- The symmetric algebra of the stalk of a module sheaf. -/
abbrev target (F : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  (RingedSpace.stalkModuleCat F x).symmetricAlgebra

/-- The canonical identification of the stalk of the sectionwise symmetric-algebra presheaf
with the stalk of its module sheafification. -/
noncomputable abbrev sheafificationIso (F : X.Modules) (x : X) :=
  TopCat.Sheaf.moduleSheafificationStalkIso X.sheaf (SymmetricAlg.presheaf F) x

/-- Lemma 17.21.2 (01CH), symmetric case: the canonical forward comparison from the stalk of
the symmetric-algebra sheaf to the symmetric algebra of the stalk module. -/
@[stacks 01CH "symmetric algebra stalk comparison"]
noncomputable def comparison (F : X.Modules) (x : X) : source F x ⟶ target F x :=
  (sheafificationIso F x).inv ≫
    PresheafOfModules.SymmetricAlgebra.Stalk.comparison (R := X.presheaf) F.val x

/-- The explicit inverse symmetric-algebra stalk comparison, transported through
sheafification. -/
@[stacks 01CH "inverse symmetric algebra stalk comparison"]
noncomputable def comparisonInv (F : X.Modules) (x : X) : target F x ⟶ source F x :=
  PresheafOfModules.SymmetricAlgebra.Stalk.comparisonInv
      (R := X.presheaf) F.val x ≫
    (sheafificationIso F x).hom

/-- The symmetric-algebra stalk comparison followed by its explicit inverse is the identity. -/
@[simp]
theorem comparison_comp_comparisonInv (F : X.Modules) (x : X) :
    comparison F x ≫ comparisonInv F x = 𝟙 (source F x) := by
  exact ((sheafificationIso F x).symm ≪≫
    PresheafOfModules.SymmetricAlgebra.Stalk.comparisonIso (R := X.presheaf) F.val x).hom_inv_id

/-- The explicit inverse symmetric-algebra stalk comparison followed by the forward comparison
is the identity. -/
@[simp]
theorem comparisonInv_comp_comparison (F : X.Modules) (x : X) :
    comparisonInv F x ≫ comparison F x = 𝟙 (target F x) := by
  exact ((sheafificationIso F x).symm ≪≫
    PresheafOfModules.SymmetricAlgebra.Stalk.comparisonIso (R := X.presheaf) F.val x).inv_hom_id

/-- Lemma 17.21.2 (01CH), symmetric case: the symmetric-algebra stalk comparison is an
isomorphism. -/
@[stacks 01CH "symmetric algebra stalk comparison is an isomorphism", instance]
instance comparison_isIso (F : X.Modules) (x : X) : IsIso (comparison F x) := by
  exact ⟨⟨comparisonInv F x, comparison_comp_comparisonInv F x,
    comparisonInv_comp_comparison F x⟩⟩

/-- The explicit isomorphism-valued form is the preferred downstream API. -/
@[stacks 01CH "symmetric algebra stalk comparison isomorphism"]
noncomputable def comparisonIso (F : X.Modules) (x : X) :
    source F x ≅ target F x :=
  (sheafificationIso F x).symm ≪≫
    PresheafOfModules.SymmetricAlgebra.Stalk.comparisonIso
      (R := X.presheaf) F.val x

/-- The forward map of `comparisonIso` is the canonical comparison morphism. -/
@[simp]
theorem comparisonIso_hom (F : X.Modules) (x : X) :
    (comparisonIso F x).hom = comparison F x := by
  rfl

/-- The inverse map of `comparisonIso` is the transported universal-lift comparison. -/
@[simp]
theorem comparisonIso_inv (F : X.Modules) (x : X) :
    (comparisonIso F x).inv = comparisonInv F x := by
  rfl

/-- The explicit inverse symmetric-algebra stalk comparison is an isomorphism. -/
instance comparisonInv_isIso (F : X.Modules) (x : X) :
    IsIso (comparisonInv F x) := by
  exact ⟨⟨comparison F x, comparisonInv_comp_comparison F x,
    comparison_comp_comparisonInv F x⟩⟩

/-- The symmetric-algebra stalk comparison sends the germ of a local degree-one generator to
the degree-one generator of the corresponding module germ. -/
@[stacks 01CH "symmetric algebra stalk comparison on germs of degree-one generators"]
theorem comparison_germ_ι (F : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    comparison F x
        (TopCat.Presheaf.germ (SymmetricAlg.sheaf F).val.presheaf U x hx
          ((SymmetricAlg.ι F).val.app (op U) m)) =
      ModuleCat.symmetricAlgebra.ι (RingedSpace.stalkModuleCat F x)
        (TopCat.Presheaf.germ F.val.presheaf U x hx m) := by
  have hι := congrArg
    (fun k : F.val.presheaf ⟶ (SymmetricAlg.sheaf F).val.presheaf ↦ k.app (op U) m)
    (algebraSheafification_lift_toPresheaf F (SymmetricAlg.presheaf F) (SymmetricAlg.presheafι F))
  change (SymmetricAlg.ι F).val.app (op U) m =
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app (SymmetricAlg.presheaf F)).app (op U)
        ((SymmetricAlg.presheafι F).app (op U) m) at hι
  change PresheafOfModules.SymmetricAlgebra.Stalk.comparison (R := X.presheaf) F.val x
    (TopCat.Sheaf.moduleSheafificationStalkComparisonInv X.sheaf (SymmetricAlg.presheaf F) x
      (TopCat.Presheaf.germ (SymmetricAlg.sheaf F).val.presheaf U x hx
        ((SymmetricAlg.ι F).val.app (op U) m))) = _
  rw [hι]
  have hs := TopCat.Sheaf.moduleSheafificationStalkComparisonInv_germ
    X.sheaf (SymmetricAlg.presheaf F) x U hx ((SymmetricAlg.presheafι F).app (op U) m)
  exact (congrArg (PresheafOfModules.SymmetricAlgebra.Stalk.comparison (R := X.presheaf) F.val x) hs).trans
    (PresheafOfModules.SymmetricAlgebra.Stalk.comparison_germ_ι (R := X.presheaf) F.val x U hx m)

/-- The inverse symmetric-algebra stalk comparison sends a degree-one generator of a module
germ to the germ of the corresponding sheaf generator. -/
@[stacks 01CH "inverse symmetric algebra stalk comparison on germ generators"]
theorem comparisonInv_germ_ι (F : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    comparisonInv F x
        (ModuleCat.symmetricAlgebra.ι (RingedSpace.stalkModuleCat F x)
          (TopCat.Presheaf.germ F.val.presheaf U x hx m)) =
      TopCat.Presheaf.germ (SymmetricAlg.sheaf F).val.presheaf U x hx
        ((SymmetricAlg.ι F).val.app (op U) m) := by
  rw [← comparison_germ_ι F x U hx m]
  change (comparison F x ≫ comparisonInv F x)
    (TopCat.Presheaf.germ (SymmetricAlg.sheaf F).val.presheaf U x hx
      ((SymmetricAlg.ι F).val.app (op U) m)) = _
  rw [comparison_comp_comparisonInv]
  rfl

/-- The symmetric-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "symmetric algebra stalk comparison preserves degree-one inclusion"]
theorem comparison_ι (F : X.Modules) (x : X) :
    RingedSpace.moduleStalkHom x (SymmetricAlg.ι F) ≫ comparison F x =
      ModuleCat.symmetricAlgebra.ιHom (RingedSpace.stalkModuleCat F x) := by
  ext m
  obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
  change comparison F x
    ((RingedSpace.moduleStalkHom x (SymmetricAlg.ι F)).hom
      (TopCat.Presheaf.germ F.val.presheaf U x hx s)) = _
  have hg : ((RingedSpace.moduleStalkHom x (SymmetricAlg.ι F)).hom
      (TopCat.Presheaf.germ F.val.presheaf U x hx s)) =
      TopCat.Presheaf.germ (SymmetricAlg.sheaf F).val.presheaf U x hx
        ((SymmetricAlg.ι F).val.app (op U) s) :=
    SheafOfModules.stalkFunctorOfCommRing_map_germ
      (𝒪 := X.sheaf) (SymmetricAlg.ι F) U x hx s
  rw [hg]
  exact comparison_germ_ι F x U hx s

/-- The inverse symmetric-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "inverse symmetric algebra stalk comparison preserves degree one"]
theorem comparisonInv_ι (F : X.Modules) (x : X) :
    ModuleCat.symmetricAlgebra.ιHom (RingedSpace.stalkModuleCat F x) ≫
        comparisonInv F x =
      RingedSpace.moduleStalkHom x (SymmetricAlg.ι F) := by
  apply (cancel_mono (comparison F x)).1
  rw [Category.assoc, comparisonInv_comp_comparison, Category.comp_id, comparison_ι]

/-- The symmetric-algebra stalk comparison preserves the multiplicative unit. -/
@[reassoc, stacks 01CH "symmetric algebra stalk comparison preserves the unit"]
theorem comparison_one (F : X.Modules) (x : X) :
    RingedSpace.moduleStalkHom x (SymmetricAlg.one F) ≫ comparison F x =
      RingedSpace.moduleStalkHom x (RingedSpace.unitIsoTensorUnit X).inv ≫
        RingedSpace.unitStalkLinearMap x ≫
          ModuleCat.symmetricAlgebra.one (RingedSpace.stalkModuleCat F x) := sorry

/-- The symmetric-algebra stalk comparison preserves multiplication. -/
@[reassoc, stacks 01CH "symmetric algebra stalk comparison preserves multiplication"]
theorem comparison_mul (F : X.Modules) (x : X) :
    RingedSpace.moduleStalkHom x (SymmetricAlg.mul F) ≫ comparison F x =
      RingedSpace.Tensor.Stalk.comparison
          (SymmetricAlg.sheaf F) (SymmetricAlg.sheaf F) x ≫
        tensorHom (comparison F x) (comparison F x) ≫
          ModuleCat.symmetricAlgebra.mul (RingedSpace.stalkModuleCat F x) := sorry

/-- The symmetric-algebra stalk comparison is natural in the module sheaf. -/
@[stacks 01CH "symmetric algebra stalk comparison naturality"]
theorem comparison_naturality {F G : X.Modules} (f : F ⟶ G) (x : X) :
    CommSq
      (RingedSpace.moduleStalkHom x (SymmetricAlg.map f))
      (comparison F x)
      (comparison G x)
      (ModuleCat.symmetricAlgebra.map (RingedSpace.moduleStalkHom x f)) := by
  constructor
  change RingedSpace.moduleStalkHom x (SymmetricAlg.map f) ≫
      ((sheafificationIso G x).inv ≫
        PresheafOfModules.SymmetricAlgebra.Stalk.comparison (R := X.presheaf) G.val x) =
    ((sheafificationIso F x).inv ≫
      PresheafOfModules.SymmetricAlgebra.Stalk.comparison (R := X.presheaf) F.val x) ≫
        ModuleCat.symmetricAlgebra.map (RingedSpace.moduleStalkHom x f)
  have h : RingedSpace.moduleStalkHom x (SymmetricAlg.map f) ≫
      (sheafificationIso G x).inv =
      (sheafificationIso F x).inv ≫
        PresheafOfModules.stalkMapOfCommRing
          (PresheafOfModules.SymmetricAlgebra.hom X.presheaf f.val) x :=
    TopCat.Sheaf.moduleSheafificationStalkComparisonInv_naturality
      X.sheaf (PresheafOfModules.SymmetricAlgebra.hom X.presheaf f.val) x
  have h' : PresheafOfModules.stalkMapOfCommRing
      (PresheafOfModules.SymmetricAlgebra.hom X.presheaf f.val) x ≫
        PresheafOfModules.SymmetricAlgebra.Stalk.comparison (R := X.presheaf) G.val x =
      PresheafOfModules.SymmetricAlgebra.Stalk.comparison (R := X.presheaf) F.val x ≫
        ModuleCat.symmetricAlgebra.map (RingedSpace.moduleStalkHom x f) :=
    (PresheafOfModules.SymmetricAlgebra.Stalk.comparison_naturality (R := X.presheaf) f.val x).w
  rw [← Category.assoc, h]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ (sheafificationIso F x).inv ≫ k) h').trans
      (Category.assoc _ _ _).symm)

/-- The explicit inverse symmetric-algebra stalk comparison is natural in the module sheaf. -/
@[stacks 01CH "inverse symmetric algebra stalk comparison naturality"]
theorem comparisonInv_naturality {F G : X.Modules} (f : F ⟶ G) (x : X) :
    ModuleCat.symmetricAlgebra.map (RingedSpace.moduleStalkHom x f) ≫
        comparisonInv G x =
      comparisonInv F x ≫ RingedSpace.moduleStalkHom x (SymmetricAlg.map f) := by
  apply (cancel_mono (comparison G x)).1
  simp only [Category.assoc, comparisonInv_comp_comparison, Category.comp_id]
  rw [(comparison_naturality f x).w, ← Category.assoc,
    comparisonInv_comp_comparison, Category.id_comp]

/-- Lemma 17.21.2 (01CH), symmetric case: the stalk comparisons assemble into a natural
transformation in the module sheaf. -/
@[stacks 01CH "symmetric algebra stalk natural transformation"]
noncomputable def natTrans (x : X) :
    SymmetricAlg.functor X ⋙ X.stalkModuleFunctor x ⟶
      X.stalkModuleFunctor x ⋙ ModuleCat.symmetricAlgebra.functor (X.presheaf.stalk x) :=
  { app := fun F ↦ comparison F x
    naturality := fun {F G} f ↦ (comparison_naturality (F := F) (G := G) f x).w }

/-- The explicit inverse symmetric-algebra stalk comparisons form a natural transformation. -/
@[stacks 01CH "inverse symmetric algebra stalk natural transformation"]
noncomputable def invNatTrans (x : X) :
    X.stalkModuleFunctor x ⋙ ModuleCat.symmetricAlgebra.functor (X.presheaf.stalk x) ⟶
      SymmetricAlg.functor X ⋙ X.stalkModuleFunctor x where
  app F := comparisonInv F x
  naturality _ _ f := comparisonInv_naturality f x

/-- Lemma 17.21.2 (01CH), symmetric case: the symmetric-algebra stalk natural transformation is
invertible. -/
@[stacks 01CH "symmetric algebra stalk natural transformation is invertible", instance]
instance natTrans_isIso (x : X) : IsIso (natTrans x) := by
  exact ⟨⟨invNatTrans x,
    NatTrans.ext (funext fun F ↦ comparison_comp_comparisonInv F x),
    NatTrans.ext (funext fun F ↦ comparisonInv_comp_comparison F x)⟩⟩

/-- The symmetric-algebra stalk isomorphism is natural in the module sheaf. -/
@[stacks 01CH "symmetric algebra stalk comparison isomorphism naturality"]
theorem comparisonIso_naturality (x : X) {F G : X.Modules} (f : F ⟶ G) :
    (SymmetricAlg.functor X ⋙ X.stalkModuleFunctor x).map f ≫
        (comparisonIso G x).hom =
      (comparisonIso F x).hom ≫
        (X.stalkModuleFunctor x ⋙
          ModuleCat.symmetricAlgebra.functor (X.presheaf.stalk x)).map f := by
  change RingedSpace.moduleStalkHom x (SymmetricAlg.map f) ≫ comparison G x =
    comparison F x ≫ ModuleCat.symmetricAlgebra.map (RingedSpace.moduleStalkHom x f)
  exact (comparison_naturality f x).w

/-- The symmetric-algebra stalk comparison natural transformation followed by its explicit
inverse is the identity. -/
@[simp, stacks 01CH "symmetric algebra stalk natural forward-inverse law"]
theorem natTrans_hom_inv_id (x : X) :
    natTrans x ≫ invNatTrans x = 𝟙 _ := by
  apply NatTrans.ext
  funext F
  exact comparison_comp_comparisonInv F x

/-- The explicit inverse symmetric-algebra stalk natural transformation followed by the
comparison is the identity. -/
@[simp, stacks 01CH "symmetric algebra stalk natural inverse-forward law"]
theorem natTrans_inv_hom_id (x : X) :
    invNatTrans x ≫ natTrans x = 𝟙 _ := by
  apply NatTrans.ext
  funext F
  exact comparisonInv_comp_comparison F x

/-- The symmetric-algebra stalk comparisons form a natural isomorphism. -/
@[stacks 01CH "symmetric algebra stalk comparison natural isomorphism"]
noncomputable def comparisonNatIso (x : X) :
    SymmetricAlg.functor X ⋙ X.stalkModuleFunctor x ≅
      X.stalkModuleFunctor x ⋙
        ModuleCat.symmetricAlgebra.functor (X.presheaf.stalk x) where
  hom := natTrans x
  inv := invNatTrans x
  hom_inv_id := natTrans_hom_inv_id x
  inv_hom_id := natTrans_inv_hom_id x

/-- A component of `comparisonNatIso` is the pointwise symmetric-algebra comparison isomorphism. -/
@[simp, stacks 01CH "symmetric algebra stalk natural isomorphism component"]
theorem comparisonNatIso_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).app F = comparisonIso F x := by
  apply Iso.ext
  rfl

/-- The forward natural transformation of `comparisonNatIso` is `natTrans`. -/
@[simp, stacks 01CH "symmetric algebra stalk natural isomorphism hom"]
theorem comparisonNatIso_hom (x : X) :
    (comparisonNatIso x).hom = natTrans x := by
  rfl

/-- The inverse natural transformation of `comparisonNatIso` is the explicit transported
universal-lift comparison. -/
@[simp, stacks 01CH "symmetric algebra stalk natural isomorphism inverse"]
theorem comparisonNatIso_inv (x : X) :
    (comparisonNatIso x).inv = invNatTrans x := by
  rfl

/-- The forward component of `comparisonNatIso` is the canonical comparison morphism. -/
@[simp, stacks 01CH "symmetric algebra stalk natural isomorphism hom component"]
theorem comparisonNatIso_hom_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).hom.app F = comparison F x := by
  rfl

/-- The inverse component of `comparisonNatIso` is the inverse pointwise comparison. -/
@[simp, stacks 01CH "symmetric algebra stalk natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).inv.app F = comparisonInv F x := by
  rfl

end AlgebraicGeometry.RingedSpace.SymmetricAlg.Stalk

namespace AlgebraicGeometry.RingedSpace.ExteriorAlg.Stalk

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The stalk of the exterior-algebra sheaf. -/
abbrev source (F : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  RingedSpace.stalkModuleCat (ExteriorAlg.sheaf F) x

/-- The exterior algebra of the stalk of a module sheaf. -/
abbrev target (F : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  (RingedSpace.stalkModuleCat F x).exteriorAlgebra

/-- The canonical identification of the stalk of the sectionwise exterior-algebra presheaf with
the stalk of its module sheafification. -/
noncomputable abbrev sheafificationIso (F : X.Modules) (x : X) :=
  TopCat.Sheaf.moduleSheafificationStalkIso X.sheaf (ExteriorAlg.presheaf F) x

/-- Lemma 17.21.2 (01CH), exterior case: the canonical forward comparison from the stalk of the
exterior-algebra sheaf to the exterior algebra of the stalk module. -/
@[stacks 01CH "exterior algebra stalk comparison"]
noncomputable def comparison (F : X.Modules) (x : X) : source F x ⟶ target F x :=
  (sheafificationIso F x).inv ≫
    PresheafOfModules.ExteriorAlgebra.Stalk.comparison (R := X.presheaf) F.val x

/-- The explicit inverse exterior-algebra stalk comparison, transported through
sheafification. -/
@[stacks 01CH "inverse exterior algebra stalk comparison"]
noncomputable def comparisonInv (F : X.Modules) (x : X) : target F x ⟶ source F x :=
  PresheafOfModules.ExteriorAlgebra.Stalk.comparisonInv
      (R := X.presheaf) F.val x ≫
    (sheafificationIso F x).hom

/-- The exterior-algebra stalk comparison followed by its explicit inverse is the identity. -/
@[simp]
theorem comparison_comp_comparisonInv (F : X.Modules) (x : X) :
    comparison F x ≫ comparisonInv F x = 𝟙 (source F x) := by
  exact ((sheafificationIso F x).symm ≪≫
    PresheafOfModules.ExteriorAlgebra.Stalk.comparisonIso (R := X.presheaf) F.val x).hom_inv_id

/-- The explicit inverse exterior-algebra stalk comparison followed by the forward comparison
is the identity. -/
@[simp]
theorem comparisonInv_comp_comparison (F : X.Modules) (x : X) :
    comparisonInv F x ≫ comparison F x = 𝟙 (target F x) := by
  exact ((sheafificationIso F x).symm ≪≫
    PresheafOfModules.ExteriorAlgebra.Stalk.comparisonIso (R := X.presheaf) F.val x).inv_hom_id

/-- Lemma 17.21.2 (01CH), exterior case: the exterior-algebra stalk comparison is an
isomorphism. -/
@[stacks 01CH "exterior algebra stalk comparison is an isomorphism", instance]
instance comparison_isIso (F : X.Modules) (x : X) : IsIso (comparison F x) := by
  exact ⟨⟨comparisonInv F x, comparison_comp_comparisonInv F x,
    comparisonInv_comp_comparison F x⟩⟩

/-- The explicit isomorphism-valued form is the preferred downstream API. -/
@[stacks 01CH "exterior algebra stalk comparison isomorphism"]
noncomputable def comparisonIso (F : X.Modules) (x : X) :
    source F x ≅ target F x :=
  (sheafificationIso F x).symm ≪≫
    PresheafOfModules.ExteriorAlgebra.Stalk.comparisonIso
      (R := X.presheaf) F.val x

/-- The forward map of `comparisonIso` is the canonical comparison morphism. -/
@[simp]
theorem comparisonIso_hom (F : X.Modules) (x : X) :
    (comparisonIso F x).hom = comparison F x := by
  rfl

/-- The inverse map of `comparisonIso` is the transported universal-lift comparison. -/
@[simp]
theorem comparisonIso_inv (F : X.Modules) (x : X) :
    (comparisonIso F x).inv = comparisonInv F x := by
  rfl

/-- The explicit inverse exterior-algebra stalk comparison is an isomorphism. -/
instance comparisonInv_isIso (F : X.Modules) (x : X) :
    IsIso (comparisonInv F x) := by
  exact ⟨⟨comparison F x, comparisonInv_comp_comparison F x,
    comparison_comp_comparisonInv F x⟩⟩

/-- The exterior-algebra stalk comparison sends the germ of a local degree-one generator to the
degree-one generator of the corresponding module germ. -/
@[stacks 01CH "exterior algebra stalk comparison on germs of degree-one generators"]
theorem comparison_germ_ι (F : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    comparison F x
        (TopCat.Presheaf.germ (ExteriorAlg.sheaf F).val.presheaf U x hx
          ((ExteriorAlg.ι F).val.app (op U) m)) =
      ModuleCat.exteriorAlgebra.ι (RingedSpace.stalkModuleCat F x)
        (TopCat.Presheaf.germ F.val.presheaf U x hx m) := by
  have hι := congrArg
    (fun k : F.val.presheaf ⟶ (ExteriorAlg.sheaf F).val.presheaf ↦ k.app (op U) m)
    (algebraSheafification_lift_toPresheaf F (ExteriorAlg.presheaf F) (ExteriorAlg.presheafι F))
  change (ExteriorAlg.ι F).val.app (op U) m =
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app (ExteriorAlg.presheaf F)).app (op U)
        ((ExteriorAlg.presheafι F).app (op U) m) at hι
  change PresheafOfModules.ExteriorAlgebra.Stalk.comparison (R := X.presheaf) F.val x
    (TopCat.Sheaf.moduleSheafificationStalkComparisonInv X.sheaf (ExteriorAlg.presheaf F) x
      (TopCat.Presheaf.germ (ExteriorAlg.sheaf F).val.presheaf U x hx
        ((ExteriorAlg.ι F).val.app (op U) m))) = _
  rw [hι]
  have hs := TopCat.Sheaf.moduleSheafificationStalkComparisonInv_germ
    X.sheaf (ExteriorAlg.presheaf F) x U hx ((ExteriorAlg.presheafι F).app (op U) m)
  exact (congrArg (PresheafOfModules.ExteriorAlgebra.Stalk.comparison (R := X.presheaf) F.val x) hs).trans
    (PresheafOfModules.ExteriorAlgebra.Stalk.comparison_germ_ι (R := X.presheaf) F.val x U hx m)

/-- The inverse exterior-algebra stalk comparison sends a degree-one generator of a module
germ to the germ of the corresponding sheaf generator. -/
@[stacks 01CH "inverse exterior algebra stalk comparison on germ generators"]
theorem comparisonInv_germ_ι (F : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    comparisonInv F x
        (ModuleCat.exteriorAlgebra.ι (RingedSpace.stalkModuleCat F x)
          (TopCat.Presheaf.germ F.val.presheaf U x hx m)) =
      TopCat.Presheaf.germ (ExteriorAlg.sheaf F).val.presheaf U x hx
        ((ExteriorAlg.ι F).val.app (op U) m) := by
  rw [← comparison_germ_ι F x U hx m]
  change (comparison F x ≫ comparisonInv F x)
    (TopCat.Presheaf.germ (ExteriorAlg.sheaf F).val.presheaf U x hx
      ((ExteriorAlg.ι F).val.app (op U) m)) = _
  rw [comparison_comp_comparisonInv]
  rfl

/-- The exterior-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "exterior algebra stalk comparison preserves degree-one inclusion"]
theorem comparison_ι (F : X.Modules) (x : X) :
    RingedSpace.moduleStalkHom x (ExteriorAlg.ι F) ≫ comparison F x =
      ModuleCat.exteriorAlgebra.ιHom (RingedSpace.stalkModuleCat F x) := by
  ext m
  obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
  change comparison F x
    ((RingedSpace.moduleStalkHom x (ExteriorAlg.ι F)).hom
      (TopCat.Presheaf.germ F.val.presheaf U x hx s)) = _
  have hg : ((RingedSpace.moduleStalkHom x (ExteriorAlg.ι F)).hom
      (TopCat.Presheaf.germ F.val.presheaf U x hx s)) =
      TopCat.Presheaf.germ (ExteriorAlg.sheaf F).val.presheaf U x hx
        ((ExteriorAlg.ι F).val.app (op U) s) :=
    SheafOfModules.stalkFunctorOfCommRing_map_germ
      (𝒪 := X.sheaf) (ExteriorAlg.ι F) U x hx s
  rw [hg]
  exact comparison_germ_ι F x U hx s

/-- The inverse exterior-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "inverse exterior algebra stalk comparison preserves degree one"]
theorem comparisonInv_ι (F : X.Modules) (x : X) :
    ModuleCat.exteriorAlgebra.ιHom (RingedSpace.stalkModuleCat F x) ≫
        comparisonInv F x =
      RingedSpace.moduleStalkHom x (ExteriorAlg.ι F) := by
  apply (cancel_mono (comparison F x)).1
  rw [Category.assoc, comparisonInv_comp_comparison, Category.comp_id, comparison_ι]

/-- The exterior-algebra stalk comparison preserves the multiplicative unit. -/
@[reassoc, stacks 01CH "exterior algebra stalk comparison preserves the unit"]
theorem comparison_one (F : X.Modules) (x : X) :
    RingedSpace.moduleStalkHom x (ExteriorAlg.one F) ≫ comparison F x =
      RingedSpace.moduleStalkHom x (RingedSpace.unitIsoTensorUnit X).inv ≫
        RingedSpace.unitStalkLinearMap x ≫
          ModuleCat.exteriorAlgebra.one (RingedSpace.stalkModuleCat F x) := sorry

/-- The exterior-algebra stalk comparison preserves multiplication. -/
@[reassoc, stacks 01CH "exterior algebra stalk comparison preserves multiplication"]
theorem comparison_mul (F : X.Modules) (x : X) :
    RingedSpace.moduleStalkHom x (ExteriorAlg.mul F) ≫ comparison F x =
      RingedSpace.Tensor.Stalk.comparison (ExteriorAlg.sheaf F) (ExteriorAlg.sheaf F) x ≫
        tensorHom (comparison F x) (comparison F x) ≫
          ModuleCat.exteriorAlgebra.mul (RingedSpace.stalkModuleCat F x) := sorry

/-- The exterior-algebra stalk comparison is natural in the module sheaf. -/
@[stacks 01CH "exterior algebra stalk comparison naturality"]
theorem comparison_naturality {F G : X.Modules} (f : F ⟶ G) (x : X) :
    CommSq
      (RingedSpace.moduleStalkHom x (ExteriorAlg.map f))
      (comparison F x)
      (comparison G x)
      (ModuleCat.exteriorAlgebra.map (RingedSpace.moduleStalkHom x f)) := by
  constructor
  change RingedSpace.moduleStalkHom x (ExteriorAlg.map f) ≫
      ((sheafificationIso G x).inv ≫
        PresheafOfModules.ExteriorAlgebra.Stalk.comparison (R := X.presheaf) G.val x) =
    ((sheafificationIso F x).inv ≫
      PresheafOfModules.ExteriorAlgebra.Stalk.comparison (R := X.presheaf) F.val x) ≫
        ModuleCat.exteriorAlgebra.map (RingedSpace.moduleStalkHom x f)
  have h : RingedSpace.moduleStalkHom x (ExteriorAlg.map f) ≫
      (sheafificationIso G x).inv =
      (sheafificationIso F x).inv ≫
        PresheafOfModules.stalkMapOfCommRing
          (PresheafOfModules.ExteriorAlgebra.hom X.presheaf f.val) x :=
    TopCat.Sheaf.moduleSheafificationStalkComparisonInv_naturality
      X.sheaf (PresheafOfModules.ExteriorAlgebra.hom X.presheaf f.val) x
  have h' : PresheafOfModules.stalkMapOfCommRing
      (PresheafOfModules.ExteriorAlgebra.hom X.presheaf f.val) x ≫
        PresheafOfModules.ExteriorAlgebra.Stalk.comparison (R := X.presheaf) G.val x =
      PresheafOfModules.ExteriorAlgebra.Stalk.comparison (R := X.presheaf) F.val x ≫
        ModuleCat.exteriorAlgebra.map (RingedSpace.moduleStalkHom x f) :=
    (PresheafOfModules.ExteriorAlgebra.Stalk.comparison_naturality (R := X.presheaf) f.val x).w
  rw [← Category.assoc, h]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ (sheafificationIso F x).inv ≫ k) h').trans
      (Category.assoc _ _ _).symm)

/-- The explicit inverse exterior-algebra stalk comparison is natural in the module sheaf. -/
@[stacks 01CH "inverse exterior algebra stalk comparison naturality"]
theorem comparisonInv_naturality {F G : X.Modules} (f : F ⟶ G) (x : X) :
    ModuleCat.exteriorAlgebra.map (RingedSpace.moduleStalkHom x f) ≫
        comparisonInv G x =
      comparisonInv F x ≫ RingedSpace.moduleStalkHom x (ExteriorAlg.map f) := by
  apply (cancel_mono (comparison G x)).1
  simp only [Category.assoc, comparisonInv_comp_comparison, Category.comp_id]
  rw [(comparison_naturality f x).w, ← Category.assoc,
    comparisonInv_comp_comparison, Category.id_comp]

/-- Lemma 17.21.2 (01CH), exterior case: the stalk comparisons assemble into a natural
transformation in the module sheaf. -/
@[stacks 01CH "exterior algebra stalk natural transformation"]
noncomputable def natTrans (x : X) :
    ExteriorAlg.functor X ⋙ X.stalkModuleFunctor x ⟶
      X.stalkModuleFunctor x ⋙ ModuleCat.exteriorAlgebra.functor (X.presheaf.stalk x) :=
  { app := fun F ↦ comparison F x
    naturality := fun {F G} f ↦ (comparison_naturality (F := F) (G := G) f x).w }

/-- The explicit inverse exterior-algebra stalk comparisons form a natural transformation. -/
@[stacks 01CH "inverse exterior algebra stalk natural transformation"]
noncomputable def invNatTrans (x : X) :
    X.stalkModuleFunctor x ⋙ ModuleCat.exteriorAlgebra.functor (X.presheaf.stalk x) ⟶
      ExteriorAlg.functor X ⋙ X.stalkModuleFunctor x where
  app F := comparisonInv F x
  naturality _ _ f := comparisonInv_naturality f x

/-- Lemma 17.21.2 (01CH), exterior case: the exterior-algebra stalk natural transformation is
invertible. -/
@[stacks 01CH "exterior algebra stalk natural transformation is invertible", instance]
instance natTrans_isIso (x : X) : IsIso (natTrans x) := by
  exact ⟨⟨invNatTrans x,
    NatTrans.ext (funext fun F ↦ comparison_comp_comparisonInv F x),
    NatTrans.ext (funext fun F ↦ comparisonInv_comp_comparison F x)⟩⟩

/-- The exterior-algebra stalk isomorphism is natural in the module sheaf. -/
@[stacks 01CH "exterior algebra stalk comparison isomorphism naturality"]
theorem comparisonIso_naturality (x : X) {F G : X.Modules} (f : F ⟶ G) :
    (ExteriorAlg.functor X ⋙ X.stalkModuleFunctor x).map f ≫
        (comparisonIso G x).hom =
      (comparisonIso F x).hom ≫
        (X.stalkModuleFunctor x ⋙
          ModuleCat.exteriorAlgebra.functor (X.presheaf.stalk x)).map f := by
  change RingedSpace.moduleStalkHom x (ExteriorAlg.map f) ≫ comparison G x =
    comparison F x ≫ ModuleCat.exteriorAlgebra.map (RingedSpace.moduleStalkHom x f)
  exact (comparison_naturality f x).w

/-- The exterior-algebra stalk comparison natural transformation followed by its explicit
inverse is the identity. -/
@[simp, stacks 01CH "exterior algebra stalk natural forward-inverse law"]
theorem natTrans_hom_inv_id (x : X) :
    natTrans x ≫ invNatTrans x = 𝟙 _ := by
  apply NatTrans.ext
  funext F
  exact comparison_comp_comparisonInv F x

/-- The explicit inverse exterior-algebra stalk natural transformation followed by the
comparison is the identity. -/
@[simp, stacks 01CH "exterior algebra stalk natural inverse-forward law"]
theorem natTrans_inv_hom_id (x : X) :
    invNatTrans x ≫ natTrans x = 𝟙 _ := by
  apply NatTrans.ext
  funext F
  exact comparisonInv_comp_comparison F x

/-- The exterior-algebra stalk comparisons form a natural isomorphism. -/
@[stacks 01CH "exterior algebra stalk comparison natural isomorphism"]
noncomputable def comparisonNatIso (x : X) :
    ExteriorAlg.functor X ⋙ X.stalkModuleFunctor x ≅
      X.stalkModuleFunctor x ⋙
        ModuleCat.exteriorAlgebra.functor (X.presheaf.stalk x) where
  hom := natTrans x
  inv := invNatTrans x
  hom_inv_id := natTrans_hom_inv_id x
  inv_hom_id := natTrans_inv_hom_id x

/-- A component of `comparisonNatIso` is the pointwise exterior-algebra comparison isomorphism. -/
@[simp, stacks 01CH "exterior algebra stalk natural isomorphism component"]
theorem comparisonNatIso_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).app F = comparisonIso F x := by
  apply Iso.ext
  rfl

/-- The forward natural transformation of `comparisonNatIso` is `natTrans`. -/
@[simp, stacks 01CH "exterior algebra stalk natural isomorphism hom"]
theorem comparisonNatIso_hom (x : X) :
    (comparisonNatIso x).hom = natTrans x := by
  rfl

/-- The inverse natural transformation of `comparisonNatIso` is the explicit transported
universal-lift comparison. -/
@[simp, stacks 01CH "exterior algebra stalk natural isomorphism inverse"]
theorem comparisonNatIso_inv (x : X) :
    (comparisonNatIso x).inv = invNatTrans x := by
  rfl

/-- The forward component of `comparisonNatIso` is the canonical comparison morphism. -/
@[simp, stacks 01CH "exterior algebra stalk natural isomorphism hom component"]
theorem comparisonNatIso_hom_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).hom.app F = comparison F x := by
  rfl

/-- The inverse component of `comparisonNatIso` is the inverse pointwise comparison. -/
@[simp, stacks 01CH "exterior algebra stalk natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).inv.app F = comparisonInv F x := by
  rfl

end AlgebraicGeometry.RingedSpace.ExteriorAlg.Stalk
