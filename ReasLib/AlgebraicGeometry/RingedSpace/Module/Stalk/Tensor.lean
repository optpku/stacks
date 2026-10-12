/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products and stalks of module sheaves

This file transports the tensor-stalk comparison for module presheaves through module
sheafification to obtain the canonical comparison for module sheaves on a ringed space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Tensor.Stalk

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The stalk of the tensor product of two module sheaves on a ringed space. -/
abbrev source (F G : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  RingedSpace.stalkModuleCat (tensorObj F G) x

/-- The tensor product over `𝒪_{X,x}` of the stalks of two module sheaves. -/
abbrev target (F G : X.Modules) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  RingedSpace.stalkModuleCat F x ⊗ RingedSpace.stalkModuleCat G x

/-- The canonical comparison from the stalk of the pointwise tensor presheaf to the stalk of its
module sheafification. -/
noncomputable abbrev sheafificationComparison (F G : X.Modules) (x : X) :=
  TopCat.Sheaf.moduleSheafificationStalkComparison X.sheaf
    (PresheafOfModules.Monoidal.tensorObj F.val G.val) x

/-- The canonical identification of the stalk of the pointwise tensor presheaf with the stalk
of its module sheafification. -/
noncomputable abbrev sheafificationIso (F G : X.Modules) (x : X) :=
  TopCat.Sheaf.moduleSheafificationStalkIso X.sheaf
    (PresheafOfModules.Monoidal.tensorObj F.val G.val) x

/-- A pure tensor section over an open set, obtained from the pointwise tensor presheaf through
the canonical sheafification model of the sheaf tensor product. -/
noncomputable abbrev tensorSectionOver (F G : X.Modules) (U : Opens X)
    (m : F.val.obj (op U)) (n : G.val.obj (op U)) :
    (tensorObj F G).val.obj (op U) :=
  SheafOfModules.RingedSite.tensorSection X.sheaf (op U) m n

/-- The canonical forward comparison from the stalk of a sheaf tensor
product to the tensor product of the two stalk modules. -/
@[stacks 01CB "tensor product stalk comparison"]
noncomputable def comparison (F G : X.Modules) (x : X) :
    source F G x ⟶ target F G x :=
  (RingedSpace.stalkModuleFunctor x).map
      (SheafOfModules.RingedSite.ModuleSheafification.tensorObjIso X.sheaf F G).hom ≫
    (sheafificationIso F G x).inv ≫
    PresheafOfModules.Tensor.Stalk.comparison F.val G.val x

/-- The explicit inverse from the tensor product of the two module-sheaf stalks to the stalk of
their tensor product. -/
@[stacks 01CB "inverse tensor product stalk comparison"]
noncomputable def comparisonInv (F G : X.Modules) (x : X) :
    target F G x ⟶ source F G x :=
  PresheafOfModules.Tensor.Stalk.comparisonInv F.val G.val x ≫
    (sheafificationIso F G x).hom ≫
    (RingedSpace.stalkModuleFunctor x).map
      (SheafOfModules.RingedSite.ModuleSheafification.tensorObjIso X.sheaf F G).inv

/-- The sheaf tensor-stalk comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 01CB "tensor product stalk forward-inverse law"]
theorem comparison_hom_inv_id (F G : X.Modules) (x : X) :
    comparison F G x ≫ comparisonInv F G x = 𝟙 _ := sorry

/-- The explicit inverse followed by the sheaf tensor-stalk comparison is the identity. -/
@[simp, stacks 01CB "tensor product stalk inverse-forward law"]
theorem comparison_inv_hom_id (F G : X.Modules) (x : X) :
    comparisonInv F G x ≫ comparison F G x = 𝟙 _ := sorry

/-- The canonical isomorphism from the stalk of a sheaf tensor product to the tensor product of
the two stalk modules, with an explicitly owned inverse. -/
@[stacks 01CB "tensor product stalk comparison isomorphism"]
noncomputable def comparisonIso (F G : X.Modules) (x : X) :
    source F G x ≅ target F G x where
  hom := comparison F G x
  inv := comparisonInv F G x
  hom_inv_id := comparison_hom_inv_id F G x
  inv_hom_id := comparison_inv_hom_id F G x

/-- The tensor-product stalk comparison is an isomorphism. -/
@[stacks 01CB "tensor product stalk comparison is an isomorphism", instance]
instance comparison_isIso (F G : X.Modules) (x : X) :
    IsIso (comparison F G x) := sorry

/-- The forward map of `comparisonIso` is the explicit ringed-space comparison. -/
@[simp, stacks 01CB "tensor product stalk comparison isomorphism hom"]
theorem comparisonIso_hom (F G : X.Modules) (x : X) :
    (comparisonIso F G x).hom = comparison F G x := sorry

/-- The inverse map of `comparisonIso` is the explicit ringed-space tensor-stalk inverse. -/
@[simp, stacks 01CB "tensor product stalk comparison isomorphism inverse"]
theorem comparisonIso_inv (F G : X.Modules) (x : X) :
    (comparisonIso F G x).inv = comparisonInv F G x := sorry

/-- The sheaf tensor-stalk comparison sends the germ of a local pure tensor section to the pure
tensor of the corresponding germs. -/
theorem comparison_germ_tensorSectionOver (F G : X.Modules) (x : X)
    (U : Opens X) (hx : x ∈ U) (m : F.val.obj (op U)) (n : G.val.obj (op U)) :
    comparison F G x
        (TopCat.Presheaf.germ (tensorObj F G).val.presheaf U x hx
          (tensorSectionOver F G U m n)) =
      TopCat.Presheaf.germ F.val.presheaf U x hx m ⊗ₜ[X.presheaf.stalk x]
        TopCat.Presheaf.germ G.val.presheaf U x hx n := sorry

/-- The inverse comparison sends a pure tensor of local germs to the germ of the corresponding
local pure tensor section. -/
theorem comparisonInv_germ_tmul (F G : X.Modules) (x : X)
    (U : Opens X) (hx : x ∈ U) (m : F.val.obj (op U)) (n : G.val.obj (op U)) :
    comparisonInv F G x
        (TopCat.Presheaf.germ F.val.presheaf U x hx m ⊗ₜ[X.presheaf.stalk x]
          TopCat.Presheaf.germ G.val.presheaf U x hx n) =
      TopCat.Presheaf.germ (tensorObj F G).val.presheaf U x hx
        (tensorSectionOver F G U m n) := sorry

/-- The tensor-product stalk comparison is natural in both module-sheaf
arguments. -/
@[stacks 01CB "tensor product stalk comparison naturality"]
theorem comparison_naturality
    {F₁ F₂ G₁ G₂ : X.Modules}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) (x : X) :
    CommSq
      (RingedSpace.moduleStalkHom x (f ⊗ₘ g))
      (comparison F₁ G₁ x)
      (comparison F₂ G₂ x)
      (RingedSpace.moduleStalkHom x f ⊗ₘ RingedSpace.moduleStalkHom x g) := sorry

/-- The explicit inverse tensor-stalk comparison is natural in both module-sheaf arguments. -/
@[stacks 01CB "inverse tensor product stalk comparison naturality"]
theorem comparisonInv_naturality
    {F₁ F₂ G₁ G₂ : X.Modules}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) (x : X) :
    CommSq
      (RingedSpace.moduleStalkHom x f ⊗ₘ RingedSpace.moduleStalkHom x g)
      (comparisonInv F₁ G₁ x)
      (comparisonInv F₂ G₂ x)
      (RingedSpace.moduleStalkHom x (f ⊗ₘ g)) := sorry

/-- The source bifunctor for the ringed-space tensor-stalk comparison. -/
@[stacks 01CB "tensor product stalk source bifunctor"]
noncomputable def sourceFunctor (x : X) :
    (X.Modules × X.Modules) ⥤ ModuleCat (X.presheaf.stalk x) :=
  MonoidalCategory.tensor X.Modules ⋙ RingedSpace.stalkModuleFunctor x

/-- The target bifunctor for the ringed-space tensor-stalk comparison. -/
@[stacks 01CB "tensor product stalk target bifunctor"]
noncomputable def targetFunctor (x : X) :
    (X.Modules × X.Modules) ⥤ ModuleCat (X.presheaf.stalk x) :=
  Functor.prod (RingedSpace.stalkModuleFunctor x) (RingedSpace.stalkModuleFunctor x) ⋙
    MonoidalCategory.tensor (ModuleCat (X.presheaf.stalk x))

/-- The ringed-space tensor-stalk comparison as a natural transformation in both sheaf inputs. -/
@[stacks 01CB "natural tensor product stalk comparison"]
noncomputable def comparisonNatTrans (x : X) :
    sourceFunctor x ⟶ targetFunctor x where
  app p := comparison p.1 p.2 x
  naturality _ _ f := (comparison_naturality f.1 f.2 x).w

/-- The inverse ringed-space tensor-stalk comparison as a natural transformation. -/
@[stacks 01CB "natural inverse tensor product stalk comparison"]
noncomputable def comparisonInvNatTrans (x : X) :
    targetFunctor x ⟶ sourceFunctor x where
  app p := comparisonInv p.1 p.2 x
  naturality _ _ f := (comparisonInv_naturality f.1 f.2 x).w

/-- The comparison followed by its inverse natural transformation is the identity. -/
@[simp, stacks 01CB "tensor product stalk natural forward-inverse law"]
theorem comparisonNatTrans_hom_inv_id (x : X) :
    comparisonNatTrans x ≫ comparisonInvNatTrans x = 𝟙 _ := sorry

/-- The inverse followed by the comparison natural transformation is the identity. -/
@[simp, stacks 01CB "tensor product stalk natural inverse-forward law"]
theorem comparisonNatTrans_inv_hom_id (x : X) :
    comparisonInvNatTrans x ≫ comparisonNatTrans x = 𝟙 _ := sorry

/-- The isomorphism-valued ringed-space comparison is natural in both sheaf inputs. -/
@[stacks 01CB "tensor product stalk comparison isomorphism naturality"]
theorem comparisonIso_naturality (x : X)
    {p q : X.Modules × X.Modules} (f : p ⟶ q) :
    (sourceFunctor x).map f ≫ (comparisonIso q.1 q.2 x).hom =
      (comparisonIso p.1 p.2 x).hom ≫ (targetFunctor x).map f := sorry

/-- The ringed-space tensor-stalk comparison as a natural isomorphism in both sheaf inputs. -/
@[stacks 01CB "natural tensor product stalk comparison isomorphism"]
noncomputable def comparisonNatIso (x : X) :
    sourceFunctor x ≅ targetFunctor x where
  hom := comparisonNatTrans x
  inv := comparisonInvNatTrans x
  hom_inv_id := comparisonNatTrans_hom_inv_id x
  inv_hom_id := comparisonNatTrans_inv_hom_id x

/-- A component of `comparisonNatIso` is the pointwise ringed-space comparison isomorphism. -/
@[simp, stacks 01CB "tensor product stalk natural isomorphism component"]
theorem comparisonNatIso_app (x : X) (p : X.Modules × X.Modules) :
    (comparisonNatIso x).app p = comparisonIso p.1 p.2 x := sorry

/-- The forward natural transformation of `comparisonNatIso` is the explicit comparison. -/
@[simp, stacks 01CB "tensor product stalk natural isomorphism hom"]
theorem comparisonNatIso_hom (x : X) :
    (comparisonNatIso x).hom = comparisonNatTrans x := sorry

/-- The inverse natural transformation of `comparisonNatIso` is explicit. -/
@[simp, stacks 01CB "tensor product stalk natural isomorphism inverse"]
theorem comparisonNatIso_inv (x : X) :
    (comparisonNatIso x).inv = comparisonInvNatTrans x := sorry

/-- The forward component of `comparisonNatIso` is the pointwise comparison morphism. -/
@[simp, stacks 01CB "tensor product stalk natural isomorphism hom component"]
theorem comparisonNatIso_hom_app (x : X) (p : X.Modules × X.Modules) :
    (comparisonNatIso x).hom.app p = comparison p.1 p.2 x := sorry

/-- The inverse component of `comparisonNatIso` is the inverse pointwise comparison. -/
@[simp, stacks 01CB "tensor product stalk natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app (x : X) (p : X.Modules × X.Modules) :
    (comparisonNatIso x).inv.app p = comparisonInv p.1 p.2 x := sorry

end AlgebraicGeometry.RingedSpace.Tensor.Stalk
