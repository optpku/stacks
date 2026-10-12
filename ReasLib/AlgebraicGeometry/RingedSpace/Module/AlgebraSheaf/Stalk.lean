/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
    comparison F x ≫ comparisonInv F x = 𝟙 (source F x) := sorry

/-- The explicit inverse tensor-algebra stalk comparison followed by the forward comparison is
the identity. -/
@[simp]
theorem comparisonInv_comp_comparison (F : X.Modules) (x : X) :
    comparisonInv F x ≫ comparison F x = 𝟙 (target F x) := sorry

/-- Lemma 17.21.2 (01CH), tensor case: the tensor-algebra stalk comparison is an
isomorphism. -/
@[stacks 01CH "tensor algebra stalk comparison is an isomorphism", instance]
instance comparison_isIso (F : X.Modules) (x : X) : IsIso (comparison F x) := sorry

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
    (comparisonIso F x).hom = comparison F x := sorry

/-- The inverse map of `comparisonIso` is the transported universal-lift comparison. -/
@[simp]
theorem comparisonIso_inv (F : X.Modules) (x : X) :
    (comparisonIso F x).inv = comparisonInv F x := sorry

/-- The explicit inverse tensor-algebra stalk comparison is an isomorphism. -/
instance comparisonInv_isIso (F : X.Modules) (x : X) :
    IsIso (comparisonInv F x) := sorry

/-- The tensor-algebra stalk comparison sends the germ of a local degree-one generator to the
degree-one generator of the corresponding module germ. -/
@[stacks 01CH "tensor algebra stalk comparison on germs of degree-one generators"]
theorem comparison_germ_ι (F : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    comparison F x
        (TopCat.Presheaf.germ (TensorAlg.sheaf F).val.presheaf U x hx
          ((TensorAlg.ι F).val.app (op U) m)) =
      ModuleCat.tensorAlgebra.ι (RingedSpace.stalkModuleCat F x)
        (TopCat.Presheaf.germ F.val.presheaf U x hx m) := sorry

/-- The inverse tensor-algebra stalk comparison sends a degree-one generator of a module germ
to the germ of the corresponding sheaf generator. -/
@[stacks 01CH "inverse tensor algebra stalk comparison on germ generators"]
theorem comparisonInv_germ_ι (F : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    comparisonInv F x
        (ModuleCat.tensorAlgebra.ι (RingedSpace.stalkModuleCat F x)
          (TopCat.Presheaf.germ F.val.presheaf U x hx m)) =
      TopCat.Presheaf.germ (TensorAlg.sheaf F).val.presheaf U x hx
        ((TensorAlg.ι F).val.app (op U) m) := sorry

/-- The tensor-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "tensor algebra stalk comparison preserves degree-one inclusion"]
theorem comparison_ι (F : X.Modules) (x : X) :
    RingedSpace.moduleStalkHom x (TensorAlg.ι F) ≫ comparison F x =
      ModuleCat.tensorAlgebra.ιHom (RingedSpace.stalkModuleCat F x) := sorry

/-- The inverse tensor-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "inverse tensor algebra stalk comparison preserves degree one"]
theorem comparisonInv_ι (F : X.Modules) (x : X) :
    ModuleCat.tensorAlgebra.ιHom (RingedSpace.stalkModuleCat F x) ≫
        comparisonInv F x =
      RingedSpace.moduleStalkHom x (TensorAlg.ι F) := sorry

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
      (ModuleCat.tensorAlgebra.map (RingedSpace.moduleStalkHom x f)) := sorry

/-- The explicit inverse tensor-algebra stalk comparison is natural in the module sheaf. -/
@[stacks 01CH "inverse tensor algebra stalk comparison naturality"]
theorem comparisonInv_naturality {F G : X.Modules} (f : F ⟶ G) (x : X) :
    ModuleCat.tensorAlgebra.map (RingedSpace.moduleStalkHom x f) ≫
        comparisonInv G x =
      comparisonInv F x ≫ RingedSpace.moduleStalkHom x (TensorAlg.map f) := sorry

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
instance natTrans_isIso (x : X) : IsIso (natTrans x) := sorry

/-- The tensor-algebra stalk isomorphism is natural in the module sheaf. -/
@[stacks 01CH "tensor algebra stalk comparison isomorphism naturality"]
theorem comparisonIso_naturality (x : X) {F G : X.Modules} (f : F ⟶ G) :
    (TensorAlg.functor X ⋙ X.stalkModuleFunctor x).map f ≫
        (comparisonIso G x).hom =
      (comparisonIso F x).hom ≫
        (X.stalkModuleFunctor x ⋙
          ModuleCat.tensorAlgebra.functor (X.presheaf.stalk x)).map f := sorry

/-- The tensor-algebra stalk comparison natural transformation followed by its explicit inverse
is the identity. -/
@[simp, stacks 01CH "tensor algebra stalk natural forward-inverse law"]
theorem natTrans_hom_inv_id (x : X) :
    natTrans x ≫ invNatTrans x = 𝟙 _ := sorry

/-- The explicit inverse tensor-algebra stalk natural transformation followed by the comparison
is the identity. -/
@[simp, stacks 01CH "tensor algebra stalk natural inverse-forward law"]
theorem natTrans_inv_hom_id (x : X) :
    invNatTrans x ≫ natTrans x = 𝟙 _ := sorry

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
    (comparisonNatIso x).app F = comparisonIso F x := sorry

/-- The forward natural transformation of `comparisonNatIso` is `natTrans`. -/
@[simp, stacks 01CH "tensor algebra stalk natural isomorphism hom"]
theorem comparisonNatIso_hom (x : X) :
    (comparisonNatIso x).hom = natTrans x := sorry

/-- The inverse natural transformation of `comparisonNatIso` is the explicit transported
universal-lift comparison. -/
@[simp, stacks 01CH "tensor algebra stalk natural isomorphism inverse"]
theorem comparisonNatIso_inv (x : X) :
    (comparisonNatIso x).inv = invNatTrans x := sorry

/-- The forward component of `comparisonNatIso` is the canonical comparison morphism. -/
@[simp, stacks 01CH "tensor algebra stalk natural isomorphism hom component"]
theorem comparisonNatIso_hom_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).hom.app F = comparison F x := sorry

/-- The inverse component of `comparisonNatIso` is the inverse pointwise comparison. -/
@[simp, stacks 01CH "tensor algebra stalk natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).inv.app F = comparisonInv F x := sorry

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
    comparison F x ≫ comparisonInv F x = 𝟙 (source F x) := sorry

/-- The explicit inverse symmetric-algebra stalk comparison followed by the forward comparison
is the identity. -/
@[simp]
theorem comparisonInv_comp_comparison (F : X.Modules) (x : X) :
    comparisonInv F x ≫ comparison F x = 𝟙 (target F x) := sorry

/-- Lemma 17.21.2 (01CH), symmetric case: the symmetric-algebra stalk comparison is an
isomorphism. -/
@[stacks 01CH "symmetric algebra stalk comparison is an isomorphism", instance]
instance comparison_isIso (F : X.Modules) (x : X) : IsIso (comparison F x) := sorry

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
    (comparisonIso F x).hom = comparison F x := sorry

/-- The inverse map of `comparisonIso` is the transported universal-lift comparison. -/
@[simp]
theorem comparisonIso_inv (F : X.Modules) (x : X) :
    (comparisonIso F x).inv = comparisonInv F x := sorry

/-- The explicit inverse symmetric-algebra stalk comparison is an isomorphism. -/
instance comparisonInv_isIso (F : X.Modules) (x : X) :
    IsIso (comparisonInv F x) := sorry

/-- The symmetric-algebra stalk comparison sends the germ of a local degree-one generator to
the degree-one generator of the corresponding module germ. -/
@[stacks 01CH "symmetric algebra stalk comparison on germs of degree-one generators"]
theorem comparison_germ_ι (F : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    comparison F x
        (TopCat.Presheaf.germ (SymmetricAlg.sheaf F).val.presheaf U x hx
          ((SymmetricAlg.ι F).val.app (op U) m)) =
      ModuleCat.symmetricAlgebra.ι (RingedSpace.stalkModuleCat F x)
        (TopCat.Presheaf.germ F.val.presheaf U x hx m) := sorry

/-- The inverse symmetric-algebra stalk comparison sends a degree-one generator of a module
germ to the germ of the corresponding sheaf generator. -/
@[stacks 01CH "inverse symmetric algebra stalk comparison on germ generators"]
theorem comparisonInv_germ_ι (F : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    comparisonInv F x
        (ModuleCat.symmetricAlgebra.ι (RingedSpace.stalkModuleCat F x)
          (TopCat.Presheaf.germ F.val.presheaf U x hx m)) =
      TopCat.Presheaf.germ (SymmetricAlg.sheaf F).val.presheaf U x hx
        ((SymmetricAlg.ι F).val.app (op U) m) := sorry

/-- The symmetric-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "symmetric algebra stalk comparison preserves degree-one inclusion"]
theorem comparison_ι (F : X.Modules) (x : X) :
    RingedSpace.moduleStalkHom x (SymmetricAlg.ι F) ≫ comparison F x =
      ModuleCat.symmetricAlgebra.ιHom (RingedSpace.stalkModuleCat F x) := sorry

/-- The inverse symmetric-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "inverse symmetric algebra stalk comparison preserves degree one"]
theorem comparisonInv_ι (F : X.Modules) (x : X) :
    ModuleCat.symmetricAlgebra.ιHom (RingedSpace.stalkModuleCat F x) ≫
        comparisonInv F x =
      RingedSpace.moduleStalkHom x (SymmetricAlg.ι F) := sorry

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
      (ModuleCat.symmetricAlgebra.map (RingedSpace.moduleStalkHom x f)) := sorry

/-- The explicit inverse symmetric-algebra stalk comparison is natural in the module sheaf. -/
@[stacks 01CH "inverse symmetric algebra stalk comparison naturality"]
theorem comparisonInv_naturality {F G : X.Modules} (f : F ⟶ G) (x : X) :
    ModuleCat.symmetricAlgebra.map (RingedSpace.moduleStalkHom x f) ≫
        comparisonInv G x =
      comparisonInv F x ≫ RingedSpace.moduleStalkHom x (SymmetricAlg.map f) := sorry

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
instance natTrans_isIso (x : X) : IsIso (natTrans x) := sorry

/-- The symmetric-algebra stalk isomorphism is natural in the module sheaf. -/
@[stacks 01CH "symmetric algebra stalk comparison isomorphism naturality"]
theorem comparisonIso_naturality (x : X) {F G : X.Modules} (f : F ⟶ G) :
    (SymmetricAlg.functor X ⋙ X.stalkModuleFunctor x).map f ≫
        (comparisonIso G x).hom =
      (comparisonIso F x).hom ≫
        (X.stalkModuleFunctor x ⋙
          ModuleCat.symmetricAlgebra.functor (X.presheaf.stalk x)).map f := sorry

/-- The symmetric-algebra stalk comparison natural transformation followed by its explicit
inverse is the identity. -/
@[simp, stacks 01CH "symmetric algebra stalk natural forward-inverse law"]
theorem natTrans_hom_inv_id (x : X) :
    natTrans x ≫ invNatTrans x = 𝟙 _ := sorry

/-- The explicit inverse symmetric-algebra stalk natural transformation followed by the
comparison is the identity. -/
@[simp, stacks 01CH "symmetric algebra stalk natural inverse-forward law"]
theorem natTrans_inv_hom_id (x : X) :
    invNatTrans x ≫ natTrans x = 𝟙 _ := sorry

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
    (comparisonNatIso x).app F = comparisonIso F x := sorry

/-- The forward natural transformation of `comparisonNatIso` is `natTrans`. -/
@[simp, stacks 01CH "symmetric algebra stalk natural isomorphism hom"]
theorem comparisonNatIso_hom (x : X) :
    (comparisonNatIso x).hom = natTrans x := sorry

/-- The inverse natural transformation of `comparisonNatIso` is the explicit transported
universal-lift comparison. -/
@[simp, stacks 01CH "symmetric algebra stalk natural isomorphism inverse"]
theorem comparisonNatIso_inv (x : X) :
    (comparisonNatIso x).inv = invNatTrans x := sorry

/-- The forward component of `comparisonNatIso` is the canonical comparison morphism. -/
@[simp, stacks 01CH "symmetric algebra stalk natural isomorphism hom component"]
theorem comparisonNatIso_hom_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).hom.app F = comparison F x := sorry

/-- The inverse component of `comparisonNatIso` is the inverse pointwise comparison. -/
@[simp, stacks 01CH "symmetric algebra stalk natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).inv.app F = comparisonInv F x := sorry

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
    comparison F x ≫ comparisonInv F x = 𝟙 (source F x) := sorry

/-- The explicit inverse exterior-algebra stalk comparison followed by the forward comparison
is the identity. -/
@[simp]
theorem comparisonInv_comp_comparison (F : X.Modules) (x : X) :
    comparisonInv F x ≫ comparison F x = 𝟙 (target F x) := sorry

/-- Lemma 17.21.2 (01CH), exterior case: the exterior-algebra stalk comparison is an
isomorphism. -/
@[stacks 01CH "exterior algebra stalk comparison is an isomorphism", instance]
instance comparison_isIso (F : X.Modules) (x : X) : IsIso (comparison F x) := sorry

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
    (comparisonIso F x).hom = comparison F x := sorry

/-- The inverse map of `comparisonIso` is the transported universal-lift comparison. -/
@[simp]
theorem comparisonIso_inv (F : X.Modules) (x : X) :
    (comparisonIso F x).inv = comparisonInv F x := sorry

/-- The explicit inverse exterior-algebra stalk comparison is an isomorphism. -/
instance comparisonInv_isIso (F : X.Modules) (x : X) :
    IsIso (comparisonInv F x) := sorry

/-- The exterior-algebra stalk comparison sends the germ of a local degree-one generator to the
degree-one generator of the corresponding module germ. -/
@[stacks 01CH "exterior algebra stalk comparison on germs of degree-one generators"]
theorem comparison_germ_ι (F : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    comparison F x
        (TopCat.Presheaf.germ (ExteriorAlg.sheaf F).val.presheaf U x hx
          ((ExteriorAlg.ι F).val.app (op U) m)) =
      ModuleCat.exteriorAlgebra.ι (RingedSpace.stalkModuleCat F x)
        (TopCat.Presheaf.germ F.val.presheaf U x hx m) := sorry

/-- The inverse exterior-algebra stalk comparison sends a degree-one generator of a module
germ to the germ of the corresponding sheaf generator. -/
@[stacks 01CH "inverse exterior algebra stalk comparison on germ generators"]
theorem comparisonInv_germ_ι (F : X.Modules) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : F.val.obj (op U)) :
    comparisonInv F x
        (ModuleCat.exteriorAlgebra.ι (RingedSpace.stalkModuleCat F x)
          (TopCat.Presheaf.germ F.val.presheaf U x hx m)) =
      TopCat.Presheaf.germ (ExteriorAlg.sheaf F).val.presheaf U x hx
        ((ExteriorAlg.ι F).val.app (op U) m) := sorry

/-- The exterior-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "exterior algebra stalk comparison preserves degree-one inclusion"]
theorem comparison_ι (F : X.Modules) (x : X) :
    RingedSpace.moduleStalkHom x (ExteriorAlg.ι F) ≫ comparison F x =
      ModuleCat.exteriorAlgebra.ιHom (RingedSpace.stalkModuleCat F x) := sorry

/-- The inverse exterior-algebra stalk comparison preserves the degree-one inclusion. -/
@[reassoc, stacks 01CH "inverse exterior algebra stalk comparison preserves degree one"]
theorem comparisonInv_ι (F : X.Modules) (x : X) :
    ModuleCat.exteriorAlgebra.ιHom (RingedSpace.stalkModuleCat F x) ≫
        comparisonInv F x =
      RingedSpace.moduleStalkHom x (ExteriorAlg.ι F) := sorry

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
      (ModuleCat.exteriorAlgebra.map (RingedSpace.moduleStalkHom x f)) := sorry

/-- The explicit inverse exterior-algebra stalk comparison is natural in the module sheaf. -/
@[stacks 01CH "inverse exterior algebra stalk comparison naturality"]
theorem comparisonInv_naturality {F G : X.Modules} (f : F ⟶ G) (x : X) :
    ModuleCat.exteriorAlgebra.map (RingedSpace.moduleStalkHom x f) ≫
        comparisonInv G x =
      comparisonInv F x ≫ RingedSpace.moduleStalkHom x (ExteriorAlg.map f) := sorry

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
instance natTrans_isIso (x : X) : IsIso (natTrans x) := sorry

/-- The exterior-algebra stalk isomorphism is natural in the module sheaf. -/
@[stacks 01CH "exterior algebra stalk comparison isomorphism naturality"]
theorem comparisonIso_naturality (x : X) {F G : X.Modules} (f : F ⟶ G) :
    (ExteriorAlg.functor X ⋙ X.stalkModuleFunctor x).map f ≫
        (comparisonIso G x).hom =
      (comparisonIso F x).hom ≫
        (X.stalkModuleFunctor x ⋙
          ModuleCat.exteriorAlgebra.functor (X.presheaf.stalk x)).map f := sorry

/-- The exterior-algebra stalk comparison natural transformation followed by its explicit
inverse is the identity. -/
@[simp, stacks 01CH "exterior algebra stalk natural forward-inverse law"]
theorem natTrans_hom_inv_id (x : X) :
    natTrans x ≫ invNatTrans x = 𝟙 _ := sorry

/-- The explicit inverse exterior-algebra stalk natural transformation followed by the
comparison is the identity. -/
@[simp, stacks 01CH "exterior algebra stalk natural inverse-forward law"]
theorem natTrans_inv_hom_id (x : X) :
    invNatTrans x ≫ natTrans x = 𝟙 _ := sorry

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
    (comparisonNatIso x).app F = comparisonIso F x := sorry

/-- The forward natural transformation of `comparisonNatIso` is `natTrans`. -/
@[simp, stacks 01CH "exterior algebra stalk natural isomorphism hom"]
theorem comparisonNatIso_hom (x : X) :
    (comparisonNatIso x).hom = natTrans x := sorry

/-- The inverse natural transformation of `comparisonNatIso` is the explicit transported
universal-lift comparison. -/
@[simp, stacks 01CH "exterior algebra stalk natural isomorphism inverse"]
theorem comparisonNatIso_inv (x : X) :
    (comparisonNatIso x).inv = invNatTrans x := sorry

/-- The forward component of `comparisonNatIso` is the canonical comparison morphism. -/
@[simp, stacks 01CH "exterior algebra stalk natural isomorphism hom component"]
theorem comparisonNatIso_hom_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).hom.app F = comparison F x := sorry

/-- The inverse component of `comparisonNatIso` is the inverse pointwise comparison. -/
@[simp, stacks 01CH "exterior algebra stalk natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app (x : X) (F : X.Modules) :
    (comparisonNatIso x).inv.app F = comparisonInv F x := sorry

end AlgebraicGeometry.RingedSpace.ExteriorAlg.Stalk
