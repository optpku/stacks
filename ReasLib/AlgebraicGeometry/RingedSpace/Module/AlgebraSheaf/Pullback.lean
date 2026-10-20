/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Exterior
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.Symmetric
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback comparisons for algebra sheaves

The tensor, exterior, and symmetric algebra sheaves are sheafifications of their sectionwise
counterparts.  For a morphism of ringed spaces, scalar change along the structure-sheaf map gives
an explicit map between the sectionwise algebras.  Transposing its sheafification across the
pullback-pushforward adjunction produces the canonical pullback comparison.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.TensorAlg.Pullback

variable {X Y : RingedSpace.{u}}

/-- The component on an open set of the adjoint tensor-algebra pullback comparison. -/
noncomputable def app (f : X ⟶ Y) (F : Y.Modules) (U : (Opens Y)ᵒᵖ) :
    (TensorAlg.presheaf F).obj U ⟶
      (((pushforward f).obj (TensorAlg.sheaf ((pullback f).obj F))).val.obj U) :=
  ModuleCat.tensorAlgebra.mapRestrictScalars
      ((RingedSpace.Hom.commRingSheafPushforwardMap f).hom.app U).hom
      (((RingedSpace.Hom.pullbackPushforwardAdjunction f).unit.app F).val.app U) ≫
    (ModuleCat.restrictScalars
      ((RingedSpace.Hom.commRingSheafPushforwardMap f).hom.app U).hom).map
      ((SheafOfModules.RingedSite.moduleSheafificationUnitToVal X.sheaf
        (TensorAlg.presheaf ((pullback f).obj F))).app
        (op ((Opens.map f.hom.base).obj U.unop)))

/-- The components of the adjoint tensor-algebra pullback comparison commute with restriction. -/
theorem app_naturality (f : X ⟶ Y) (F : Y.Modules)
    {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V) :
    (TensorAlg.presheaf F).map i ≫
        (ModuleCat.restrictScalars (Y.presheaf.map i).hom).map (app f F V) =
      app f F U ≫ ((pushforward f).obj (TensorAlg.sheaf ((pullback f).obj F))).val.map i := sorry

/-- The presheaf morphism adjoint to the tensor-algebra pullback comparison before
sheafification. -/
noncomputable def presheaf (f : X ⟶ Y) (F : Y.Modules) :
    TensorAlg.presheaf F ⟶ ((pushforward f).obj (TensorAlg.sheaf ((pullback f).obj F))).val where
  app U := app f F U
  naturality := app_naturality f F

/-- The pushforward-side adjoint of the tensor-algebra pullback comparison. -/
noncomputable def adjoint (f : X ⟶ Y) (F : Y.Modules) :
    TensorAlg.sheaf F ⟶ (pushforward f).obj (TensorAlg.sheaf ((pullback f).obj F)) :=
  ((SheafOfModules.RingedSite.moduleSheafificationAdjunction Y.sheaf).homEquiv
    (TensorAlg.presheaf F) ((pushforward f).obj (TensorAlg.sheaf ((pullback f).obj F)))).symm
      (presheaf f F ≫
        (SheafOfModules.RingedSite.valRestrictionIso Y.sheaf
          ((pushforward f).obj (TensorAlg.sheaf ((pullback f).obj F)))).hom)

/-- Lemma 17.21.3 (01CI) (1), comparison morphism: the canonical map from the pullback of a
tensor-algebra sheaf to the tensor algebra of the pulled-back module sheaf. -/
@[stacks 01CI "(1), tensor-algebra comparison morphism"]
noncomputable def comparison (f : X ⟶ Y) (F : Y.Modules) :
    (pullback f).obj (TensorAlg.sheaf F) ⟶ TensorAlg.sheaf ((pullback f).obj F) :=
  ((RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv _ _).symm (adjoint f F)

/-- Lemma 17.21.3 (01CI) (1): pullback commutes with the tensor-algebra sheaf construction. -/
@[stacks 01CI "(1), tensor algebra", instance]
instance comparison_isIso (f : X ⟶ Y) (F : Y.Modules) :
    IsIso (comparison f F) := sorry

/- The comparison isomorphism currently has one unavoidable categorical data gate: the
  invertibility statement above.  The selected inverse is named below so downstream code does
  not repeatedly select `CategoryTheory.inv`. -/
/-- The explicit inverse of the tensor-algebra pullback comparison. -/
@[stacks 01CI "tensor-algebra pullback comparison inverse"]
noncomputable def comparisonInv (f : X ⟶ Y) (F : Y.Modules) :
    TensorAlg.sheaf ((pullback f).obj F) ⟶ (pullback f).obj (TensorAlg.sheaf F) :=
  inv (comparison f F)

/-- The tensor-algebra pullback comparison followed by its named inverse is the identity. -/
@[simp, stacks 01CI "tensor-algebra comparison forward-inverse law"]
theorem comparison_hom_inv_id (f : X ⟶ Y) (F : Y.Modules) :
    comparison f F ≫ comparisonInv f F = 𝟙 _ := sorry

/-- The named tensor-algebra inverse followed by the comparison is the identity. -/
@[simp, stacks 01CI "tensor-algebra comparison inverse-forward law"]
theorem comparison_inv_hom_id (f : X ⟶ Y) (F : Y.Modules) :
    comparisonInv f F ≫ comparison f F = 𝟙 _ := sorry

/-- The canonical tensor-algebra pullback comparison as a literal isomorphism. -/
@[stacks 01CI "tensor-algebra pullback comparison isomorphism"]
noncomputable def comparisonIso (f : X ⟶ Y) (F : Y.Modules) :
    (pullback f).obj (TensorAlg.sheaf F) ≅ TensorAlg.sheaf ((pullback f).obj F) :=
  { hom := comparison f F
    inv := comparisonInv f F
    hom_inv_id := comparison_hom_inv_id f F
    inv_hom_id := comparison_inv_hom_id f F }

/-- The forward map of the tensor-algebra pullback comparison isomorphism. -/
@[simp]
theorem comparisonIso_hom (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonIso f F).hom = comparison f F := sorry

/-- The inverse projection of the tensor-algebra comparison isomorphism is the named owner. -/
@[simp, stacks 01CI "tensor-algebra comparison isomorphism inverse"]
theorem comparisonIso_inv (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonIso f F).inv = comparisonInv f F := sorry

/-- The tensor-algebra pullback comparisons are natural in the module sheaf. -/
@[stacks 01CI "(1), tensor-algebra comparison naturality"]
theorem comparison_naturality (f : X ⟶ Y) {F G : Y.Modules} (g : F ⟶ G) :
    (pullback f).map (TensorAlg.map g) ≫ comparison f G =
      comparison f F ≫ TensorAlg.map ((pullback f).map g) := sorry

/-- The tensor-algebra pullback comparison preserves the degree-one inclusion. -/
@[stacks 01CI "(1), tensor-algebra degree-one compatibility"]
theorem comparison_ι (f : X ⟶ Y) (F : Y.Modules) :
    (pullback f).map (TensorAlg.ι F) ≫ comparison f F = TensorAlg.ι ((pullback f).obj F) := sorry

/-- The tensor-algebra pullback comparison preserves the multiplicative unit. -/
@[reassoc, stacks 01CI "(1), tensor-algebra unit compatibility"]
theorem comparison_one (f : X ⟶ Y) (F : Y.Modules) :
    Functor.LaxMonoidal.ε (pullback f) ≫
        (pullback f).map (TensorAlg.one F) ≫ comparison f F =
      TensorAlg.one ((pullback f).obj F) := sorry

/-- The tensor-algebra pullback comparison preserves multiplication. -/
@[reassoc, stacks 01CI "(1), tensor-algebra multiplication compatibility"]
theorem comparison_mul (f : X ⟶ Y) (F : Y.Modules) :
    Functor.LaxMonoidal.μ (pullback f) (TensorAlg.sheaf F) (TensorAlg.sheaf F) ≫
        (pullback f).map (TensorAlg.mul F) ≫ comparison f F =
      tensorHom (comparison f F) (comparison f F) ≫
        TensorAlg.mul ((pullback f).obj F) := sorry

/-- Lemma 17.21.3 (01CI) (1): the natural transformation expressing compatibility of
tensor-algebra sheaves with pullback. Its components are isomorphisms by
`comparison_isIso`. -/
@[stacks 01CI "(1), tensor-algebra pullback natural transformation"]
noncomputable def natTrans (f : X ⟶ Y) :
    TensorAlg.functor Y ⋙ pullback f ⟶ pullback f ⋙ TensorAlg.functor X where
  app F := comparison f F
  naturality := fun {F G} g ↦ comparison_naturality f (F := F) (G := G) g

/-- Every component of the tensor-algebra pullback natural transformation is invertible. -/
@[stacks 01CI "(1), tensor-algebra pullback natural transformation is invertible"]
instance natTrans_isIso (f : X ⟶ Y) : IsIso (natTrans f) := sorry

/-- The tensor-algebra pullback comparison isomorphism is natural in the module sheaf. -/
@[stacks 01CI "tensor-algebra pullback comparison isomorphism naturality"]
theorem comparisonIso_naturality (f : X ⟶ Y) {F G : Y.Modules} (g : F ⟶ G) :
    (TensorAlg.functor Y ⋙ pullback f).map g ≫ (comparisonIso f G).hom =
      (comparisonIso f F).hom ≫ (pullback f ⋙ TensorAlg.functor X).map g := sorry

/-- The named inverse comparisons are natural in the module sheaf. -/
@[stacks 01CI "tensor-algebra inverse comparison naturality"]
theorem comparisonInv_naturality (f : X ⟶ Y) {F G : Y.Modules} (g : F ⟶ G) :
    (pullback f ⋙ TensorAlg.functor X).map g ≫ comparisonInv f G =
      comparisonInv f F ≫ (TensorAlg.functor Y ⋙ pullback f).map g := sorry

/-- The inverse components of the tensor-algebra natural isomorphism form a named
  natural transformation. -/
@[stacks 01CI "tensor-algebra inverse pullback natural transformation"]
noncomputable def invNatTrans (f : X ⟶ Y) :
    pullback f ⋙ TensorAlg.functor X ⟶ TensorAlg.functor Y ⋙ pullback f where
  app F := comparisonInv f F
  naturality := fun {F G} g ↦ comparisonInv_naturality f g

/-- The tensor-algebra comparison and its inverse natural transformation compose to the identity. -/
@[simp, stacks 01CI "tensor-algebra natural transformation forward-inverse law"]
theorem natTrans_hom_inv_id (f : X ⟶ Y) :
    natTrans f ≫ invNatTrans f = 𝟙 _ := sorry

/-- The inverse tensor-algebra natural transformation and comparison compose to the identity. -/
@[simp, stacks 01CI "tensor-algebra natural transformation inverse-forward law"]
theorem natTrans_inv_hom_id (f : X ⟶ Y) :
    invNatTrans f ≫ natTrans f = 𝟙 _ := sorry

/-- The tensor-algebra pullback comparisons as a natural isomorphism. -/
@[stacks 01CI "tensor-algebra pullback natural isomorphism"]
noncomputable def comparisonNatIso (f : X ⟶ Y) :
    TensorAlg.functor Y ⋙ pullback f ≅ pullback f ⋙ TensorAlg.functor X where
  hom := natTrans f
  inv := invNatTrans f
  hom_inv_id := natTrans_hom_inv_id f
  inv_hom_id := natTrans_inv_hom_id f

/-- A component of the tensor-algebra pullback natural isomorphism. -/
@[simp, stacks 01CI "tensor-algebra pullback natural isomorphism component"]
theorem comparisonNatIso_app (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonNatIso f).app F = comparisonIso f F := sorry

/-- The forward transformation of the tensor-algebra pullback natural isomorphism. -/
@[simp, stacks 01CI "tensor-algebra pullback natural isomorphism hom"]
theorem comparisonNatIso_hom (f : X ⟶ Y) :
    (comparisonNatIso f).hom = natTrans f := sorry

/-- The forward component of the tensor-algebra pullback natural isomorphism. -/
@[simp, stacks 01CI "tensor-algebra pullback natural isomorphism hom component"]
theorem comparisonNatIso_hom_app (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonNatIso f).hom.app F = comparison f F := sorry

/-- The inverse transformation of the tensor-algebra natural isomorphism is `invNatTrans`. -/
@[simp, stacks 01CI "tensor-algebra pullback natural isomorphism inverse"]
theorem comparisonNatIso_inv (f : X ⟶ Y) :
    (comparisonNatIso f).inv = invNatTrans f := sorry

/-- The inverse component of the tensor-algebra pullback natural isomorphism. -/
@[simp, stacks 01CI "tensor-algebra pullback natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonNatIso f).inv.app F = comparisonInv f F := sorry

end AlgebraicGeometry.RingedSpace.TensorAlg.Pullback

namespace AlgebraicGeometry.RingedSpace.ExteriorAlg.Pullback

variable {X Y : RingedSpace.{u}}

/-- The component on an open set of the adjoint exterior-algebra pullback comparison. -/
noncomputable def app (f : X ⟶ Y) (F : Y.Modules) (U : (Opens Y)ᵒᵖ) :
    (ExteriorAlg.presheaf F).obj U ⟶
      (((pushforward f).obj (ExteriorAlg.sheaf ((pullback f).obj F))).val.obj U) :=
  ModuleCat.exteriorAlgebra.mapRestrictScalars
      ((RingedSpace.Hom.commRingSheafPushforwardMap f).hom.app U).hom
      (((RingedSpace.Hom.pullbackPushforwardAdjunction f).unit.app F).val.app U) ≫
    (ModuleCat.restrictScalars
      ((RingedSpace.Hom.commRingSheafPushforwardMap f).hom.app U).hom).map
      ((SheafOfModules.RingedSite.moduleSheafificationUnitToVal X.sheaf
        (ExteriorAlg.presheaf ((pullback f).obj F))).app
        (op ((Opens.map f.hom.base).obj U.unop)))

/-- The components of the adjoint exterior-algebra pullback comparison commute with
restriction. -/
theorem app_naturality (f : X ⟶ Y) (F : Y.Modules)
    {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V) :
    (ExteriorAlg.presheaf F).map i ≫
        (ModuleCat.restrictScalars (Y.presheaf.map i).hom).map (app f F V) =
      app f F U ≫ ((pushforward f).obj (ExteriorAlg.sheaf ((pullback f).obj F))).val.map i := sorry

/-- The presheaf morphism adjoint to the exterior-algebra pullback comparison before
sheafification. -/
noncomputable def presheaf (f : X ⟶ Y) (F : Y.Modules) :
    ExteriorAlg.presheaf F ⟶ ((pushforward f).obj (ExteriorAlg.sheaf ((pullback f).obj F))).val where
  app U := app f F U
  naturality := app_naturality f F

/-- The pushforward-side adjoint of the exterior-algebra pullback comparison. -/
noncomputable def adjoint (f : X ⟶ Y) (F : Y.Modules) :
    ExteriorAlg.sheaf F ⟶ (pushforward f).obj (ExteriorAlg.sheaf ((pullback f).obj F)) :=
  ((SheafOfModules.RingedSite.moduleSheafificationAdjunction Y.sheaf).homEquiv
    (ExteriorAlg.presheaf F) ((pushforward f).obj (ExteriorAlg.sheaf ((pullback f).obj F)))).symm
      (presheaf f F ≫
        (SheafOfModules.RingedSite.valRestrictionIso Y.sheaf
          ((pushforward f).obj (ExteriorAlg.sheaf ((pullback f).obj F)))).hom)

/-- Lemma 17.21.3 (01CI) (2), comparison morphism: the canonical map from the pullback of an
exterior-algebra sheaf to the exterior algebra of the pulled-back module sheaf. -/
@[stacks 01CI "(2), exterior-algebra comparison morphism"]
noncomputable def comparison (f : X ⟶ Y) (F : Y.Modules) :
    (pullback f).obj (ExteriorAlg.sheaf F) ⟶ ExteriorAlg.sheaf ((pullback f).obj F) :=
  ((RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv _ _).symm (adjoint f F)

/-- Lemma 17.21.3 (01CI) (2): pullback commutes with the exterior-algebra sheaf
construction. -/
@[stacks 01CI "(2), exterior algebra", instance]
instance comparison_isIso (f : X ⟶ Y) (F : Y.Modules) :
    IsIso (comparison f F) := sorry

/- The comparison isomorphism has one unavoidable categorical invertibility gate above.  The
  selected inverse is named below as the reusable data owner. -/
/-- The explicit inverse of the exterior-algebra pullback comparison. -/
@[stacks 01CI "exterior-algebra pullback comparison inverse"]
noncomputable def comparisonInv (f : X ⟶ Y) (F : Y.Modules) :
    ExteriorAlg.sheaf ((pullback f).obj F) ⟶ (pullback f).obj (ExteriorAlg.sheaf F) :=
  inv (comparison f F)

/-- The exterior-algebra pullback comparison followed by its named inverse is the identity. -/
@[simp, stacks 01CI "exterior-algebra comparison forward-inverse law"]
theorem comparison_hom_inv_id (f : X ⟶ Y) (F : Y.Modules) :
    comparison f F ≫ comparisonInv f F = 𝟙 _ := sorry

/-- The named exterior-algebra inverse followed by the comparison is the identity. -/
@[simp, stacks 01CI "exterior-algebra comparison inverse-forward law"]
theorem comparison_inv_hom_id (f : X ⟶ Y) (F : Y.Modules) :
    comparisonInv f F ≫ comparison f F = 𝟙 _ := sorry

/-- The canonical exterior-algebra pullback comparison as a literal isomorphism. -/
@[stacks 01CI "exterior-algebra pullback comparison isomorphism"]
noncomputable def comparisonIso (f : X ⟶ Y) (F : Y.Modules) :
    (pullback f).obj (ExteriorAlg.sheaf F) ≅ ExteriorAlg.sheaf ((pullback f).obj F) :=
  { hom := comparison f F
    inv := comparisonInv f F
    hom_inv_id := comparison_hom_inv_id f F
    inv_hom_id := comparison_inv_hom_id f F }

/-- The forward map of the exterior-algebra pullback comparison isomorphism. -/
@[simp]
theorem comparisonIso_hom (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonIso f F).hom = comparison f F := sorry

/-- The inverse projection of the exterior-algebra comparison isomorphism is the named owner. -/
@[simp, stacks 01CI "exterior-algebra comparison isomorphism inverse"]
theorem comparisonIso_inv (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonIso f F).inv = comparisonInv f F := sorry

/-- The exterior-algebra pullback comparisons are natural in the module sheaf. -/
@[stacks 01CI "(2), exterior-algebra comparison naturality"]
theorem comparison_naturality (f : X ⟶ Y) {F G : Y.Modules} (g : F ⟶ G) :
    (pullback f).map (ExteriorAlg.map g) ≫ comparison f G =
      comparison f F ≫ ExteriorAlg.map ((pullback f).map g) := sorry

/-- The exterior-algebra pullback comparison preserves the degree-one inclusion. -/
@[stacks 01CI "(2), exterior-algebra degree-one compatibility"]
theorem comparison_ι (f : X ⟶ Y) (F : Y.Modules) :
    (pullback f).map (ExteriorAlg.ι F) ≫ comparison f F = ExteriorAlg.ι ((pullback f).obj F) := sorry

/-- The exterior-algebra pullback comparison preserves the multiplicative unit. -/
@[reassoc, stacks 01CI "(2), exterior-algebra unit compatibility"]
theorem comparison_one (f : X ⟶ Y) (F : Y.Modules) :
    Functor.LaxMonoidal.ε (pullback f) ≫
        (pullback f).map (ExteriorAlg.one F) ≫ comparison f F =
      ExteriorAlg.one ((pullback f).obj F) := sorry

/-- The exterior-algebra pullback comparison preserves multiplication. -/
@[reassoc, stacks 01CI "(2), exterior-algebra multiplication compatibility"]
theorem comparison_mul (f : X ⟶ Y) (F : Y.Modules) :
    Functor.LaxMonoidal.μ (pullback f) (ExteriorAlg.sheaf F) (ExteriorAlg.sheaf F) ≫
        (pullback f).map (ExteriorAlg.mul F) ≫ comparison f F =
      tensorHom (comparison f F) (comparison f F) ≫
        ExteriorAlg.mul ((pullback f).obj F) := sorry

/-- Lemma 17.21.3 (01CI) (2): the natural transformation expressing compatibility of
exterior-algebra sheaves with pullback. Its components are isomorphisms by
`comparison_isIso`. -/
@[stacks 01CI "(2), exterior-algebra pullback natural transformation"]
noncomputable def natTrans (f : X ⟶ Y) :
    ExteriorAlg.functor Y ⋙ pullback f ⟶ pullback f ⋙ ExteriorAlg.functor X where
  app F := comparison f F
  naturality := fun {F G} g ↦ comparison_naturality f (F := F) (G := G) g

/-- Every component of the exterior-algebra pullback natural transformation is invertible. -/
@[stacks 01CI "(2), exterior-algebra pullback natural transformation is invertible"]
instance natTrans_isIso (f : X ⟶ Y) : IsIso (natTrans f) := sorry

/-- The exterior-algebra pullback comparison isomorphism is natural in the module sheaf. -/
@[stacks 01CI "exterior-algebra pullback comparison isomorphism naturality"]
theorem comparisonIso_naturality (f : X ⟶ Y) {F G : Y.Modules} (g : F ⟶ G) :
    (ExteriorAlg.functor Y ⋙ pullback f).map g ≫ (comparisonIso f G).hom =
      (comparisonIso f F).hom ≫
        (pullback f ⋙ ExteriorAlg.functor X).map g := sorry

/-- The named inverse comparisons are natural in the module sheaf. -/
@[stacks 01CI "exterior-algebra inverse comparison naturality"]
theorem comparisonInv_naturality (f : X ⟶ Y) {F G : Y.Modules} (g : F ⟶ G) :
    (pullback f ⋙ ExteriorAlg.functor X).map g ≫ comparisonInv f G =
      comparisonInv f F ≫ (ExteriorAlg.functor Y ⋙ pullback f).map g := sorry

/-- The inverse components of the exterior-algebra natural isomorphism form a named
  natural transformation. -/
@[stacks 01CI "exterior-algebra inverse pullback natural transformation"]
noncomputable def invNatTrans (f : X ⟶ Y) :
    pullback f ⋙ ExteriorAlg.functor X ⟶ ExteriorAlg.functor Y ⋙ pullback f where
  app F := comparisonInv f F
  naturality := fun {F G} g ↦ comparisonInv_naturality f g

/-- The exterior-algebra comparison and its inverse natural transformation compose to the identity. -/
@[simp, stacks 01CI "exterior-algebra natural transformation forward-inverse law"]
theorem natTrans_hom_inv_id (f : X ⟶ Y) :
    natTrans f ≫ invNatTrans f = 𝟙 _ := sorry

/-- The inverse exterior-algebra natural transformation and comparison compose to the identity. -/
@[simp, stacks 01CI "exterior-algebra natural transformation inverse-forward law"]
theorem natTrans_inv_hom_id (f : X ⟶ Y) :
    invNatTrans f ≫ natTrans f = 𝟙 _ := sorry

/-- The exterior-algebra pullback comparisons as a natural isomorphism. -/
@[stacks 01CI "exterior-algebra pullback natural isomorphism"]
noncomputable def comparisonNatIso (f : X ⟶ Y) :
    ExteriorAlg.functor Y ⋙ pullback f ≅ pullback f ⋙ ExteriorAlg.functor X where
  hom := natTrans f
  inv := invNatTrans f
  hom_inv_id := natTrans_hom_inv_id f
  inv_hom_id := natTrans_inv_hom_id f

/-- A component of the exterior-algebra pullback natural isomorphism. -/
@[simp, stacks 01CI "exterior-algebra pullback natural isomorphism component"]
theorem comparisonNatIso_app (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonNatIso f).app F = comparisonIso f F := sorry

/-- The forward transformation of the exterior-algebra pullback natural isomorphism. -/
@[simp, stacks 01CI "exterior-algebra pullback natural isomorphism hom"]
theorem comparisonNatIso_hom (f : X ⟶ Y) :
    (comparisonNatIso f).hom = natTrans f := sorry

/-- The forward component of the exterior-algebra pullback natural isomorphism. -/
@[simp, stacks 01CI "exterior-algebra pullback natural isomorphism hom component"]
theorem comparisonNatIso_hom_app (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonNatIso f).hom.app F = comparison f F := sorry

/-- The inverse transformation of the exterior-algebra natural isomorphism is `invNatTrans`. -/
@[simp, stacks 01CI "exterior-algebra pullback natural isomorphism inverse"]
theorem comparisonNatIso_inv (f : X ⟶ Y) :
    (comparisonNatIso f).inv = invNatTrans f := sorry

/-- The inverse component of the exterior-algebra pullback natural isomorphism. -/
@[simp, stacks 01CI "exterior-algebra pullback natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonNatIso f).inv.app F = comparisonInv f F := sorry

end AlgebraicGeometry.RingedSpace.ExteriorAlg.Pullback

namespace AlgebraicGeometry.RingedSpace.SymmetricAlg.Pullback

variable {X Y : RingedSpace.{u}}

/-- The component on an open set of the adjoint symmetric-algebra pullback comparison. -/
noncomputable def app (f : X ⟶ Y) (F : Y.Modules) (U : (Opens Y)ᵒᵖ) :
    (SymmetricAlg.presheaf F).obj U ⟶
      (((pushforward f).obj (SymmetricAlg.sheaf ((pullback f).obj F))).val.obj U) :=
  ModuleCat.symmetricAlgebra.mapRestrictScalars
      ((RingedSpace.Hom.commRingSheafPushforwardMap f).hom.app U).hom
      (((RingedSpace.Hom.pullbackPushforwardAdjunction f).unit.app F).val.app U) ≫
    (ModuleCat.restrictScalars
      ((RingedSpace.Hom.commRingSheafPushforwardMap f).hom.app U).hom).map
      ((SheafOfModules.RingedSite.moduleSheafificationUnitToVal X.sheaf
        (SymmetricAlg.presheaf ((pullback f).obj F))).app
        (op ((Opens.map f.hom.base).obj U.unop)))

/-- The components of the adjoint symmetric-algebra pullback comparison commute with
restriction. -/
theorem app_naturality (f : X ⟶ Y) (F : Y.Modules)
    {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V) :
    (SymmetricAlg.presheaf F).map i ≫
        (ModuleCat.restrictScalars (Y.presheaf.map i).hom).map (app f F V) =
      app f F U ≫
        ((pushforward f).obj (SymmetricAlg.sheaf ((pullback f).obj F))).val.map i := sorry

/-- The presheaf morphism adjoint to the symmetric-algebra pullback comparison before
sheafification. -/
noncomputable def presheaf (f : X ⟶ Y) (F : Y.Modules) :
    SymmetricAlg.presheaf F ⟶
      ((pushforward f).obj (SymmetricAlg.sheaf ((pullback f).obj F))).val where
  app U := app f F U
  naturality := app_naturality f F

/-- The pushforward-side adjoint of the symmetric-algebra pullback comparison. -/
noncomputable def adjoint (f : X ⟶ Y) (F : Y.Modules) :
    SymmetricAlg.sheaf F ⟶
      (pushforward f).obj (SymmetricAlg.sheaf ((pullback f).obj F)) :=
  ((SheafOfModules.RingedSite.moduleSheafificationAdjunction Y.sheaf).homEquiv
    (SymmetricAlg.presheaf F)
    ((pushforward f).obj (SymmetricAlg.sheaf ((pullback f).obj F)))).symm
      (presheaf f F ≫
        (SheafOfModules.RingedSite.valRestrictionIso Y.sheaf
          ((pushforward f).obj (SymmetricAlg.sheaf ((pullback f).obj F)))).hom)

/-- Lemma 17.21.3 (01CI) (3), comparison morphism: the canonical map from the pullback of a
symmetric-algebra sheaf to the symmetric algebra of the pulled-back module sheaf. -/
@[stacks 01CI "(3), symmetric-algebra comparison morphism"]
noncomputable def comparison (f : X ⟶ Y) (F : Y.Modules) :
    (pullback f).obj (SymmetricAlg.sheaf F) ⟶ SymmetricAlg.sheaf ((pullback f).obj F) :=
  ((RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv _ _).symm (adjoint f F)

/-- Lemma 17.21.3 (01CI) (3): pullback commutes with the symmetric-algebra sheaf
construction. -/
@[stacks 01CI "(3), symmetric algebra", instance]
instance comparison_isIso (f : X ⟶ Y) (F : Y.Modules) :
    IsIso (comparison f F) := sorry

/- The comparison isomorphism has one unavoidable categorical invertibility gate above.  The
  selected inverse is named below as the reusable data owner. -/
/-- The explicit inverse of the symmetric-algebra pullback comparison. -/
@[stacks 01CI "symmetric-algebra pullback comparison inverse"]
noncomputable def comparisonInv (f : X ⟶ Y) (F : Y.Modules) :
    SymmetricAlg.sheaf ((pullback f).obj F) ⟶ (pullback f).obj (SymmetricAlg.sheaf F) :=
  inv (comparison f F)

/-- The symmetric-algebra pullback comparison followed by its named inverse is the identity. -/
@[simp, stacks 01CI "symmetric-algebra comparison forward-inverse law"]
theorem comparison_hom_inv_id (f : X ⟶ Y) (F : Y.Modules) :
    comparison f F ≫ comparisonInv f F = 𝟙 _ := sorry

/-- The named symmetric-algebra inverse followed by the comparison is the identity. -/
@[simp, stacks 01CI "symmetric-algebra comparison inverse-forward law"]
theorem comparison_inv_hom_id (f : X ⟶ Y) (F : Y.Modules) :
    comparisonInv f F ≫ comparison f F = 𝟙 _ := sorry

/-- The canonical symmetric-algebra pullback comparison as a literal isomorphism. -/
@[stacks 01CI "symmetric-algebra pullback comparison isomorphism"]
noncomputable def comparisonIso (f : X ⟶ Y) (F : Y.Modules) :
    (pullback f).obj (SymmetricAlg.sheaf F) ≅ SymmetricAlg.sheaf ((pullback f).obj F) :=
  { hom := comparison f F
    inv := comparisonInv f F
    hom_inv_id := comparison_hom_inv_id f F
    inv_hom_id := comparison_inv_hom_id f F }

/-- The forward map of the symmetric-algebra pullback comparison isomorphism. -/
@[simp]
theorem comparisonIso_hom (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonIso f F).hom = comparison f F := sorry

/-- The inverse projection of the symmetric-algebra comparison isomorphism is the named owner. -/
@[simp, stacks 01CI "symmetric-algebra comparison isomorphism inverse"]
theorem comparisonIso_inv (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonIso f F).inv = comparisonInv f F := sorry

/-- The symmetric-algebra pullback comparisons are natural in the module sheaf. -/
@[stacks 01CI "(3), symmetric-algebra comparison naturality"]
theorem comparison_naturality (f : X ⟶ Y) {F G : Y.Modules} (g : F ⟶ G) :
    (pullback f).map (SymmetricAlg.map g) ≫ comparison f G =
      comparison f F ≫ SymmetricAlg.map ((pullback f).map g) := sorry

/-- The symmetric-algebra pullback comparison preserves the degree-one inclusion. -/
@[stacks 01CI "(3), symmetric-algebra degree-one compatibility"]
theorem comparison_ι (f : X ⟶ Y) (F : Y.Modules) :
    (pullback f).map (SymmetricAlg.ι F) ≫ comparison f F =
      SymmetricAlg.ι ((pullback f).obj F) := sorry

/-- The symmetric-algebra pullback comparison preserves the multiplicative unit. -/
@[reassoc, stacks 01CI "(3), symmetric-algebra unit compatibility"]
theorem comparison_one (f : X ⟶ Y) (F : Y.Modules) :
    Functor.LaxMonoidal.ε (pullback f) ≫
        (pullback f).map (SymmetricAlg.one F) ≫ comparison f F =
      SymmetricAlg.one ((pullback f).obj F) := sorry

/-- The symmetric-algebra pullback comparison preserves multiplication. -/
@[reassoc, stacks 01CI "(3), symmetric-algebra multiplication compatibility"]
theorem comparison_mul (f : X ⟶ Y) (F : Y.Modules) :
    Functor.LaxMonoidal.μ (pullback f) (SymmetricAlg.sheaf F) (SymmetricAlg.sheaf F) ≫
        (pullback f).map (SymmetricAlg.mul F) ≫ comparison f F =
      tensorHom (comparison f F) (comparison f F) ≫
        SymmetricAlg.mul ((pullback f).obj F) := sorry

/-- Lemma 17.21.3 (01CI) (3): the natural transformation expressing compatibility of
symmetric-algebra sheaves with pullback. Its components are isomorphisms by
`comparison_isIso`. -/
@[stacks 01CI "(3), symmetric-algebra pullback natural transformation"]
noncomputable def natTrans (f : X ⟶ Y) :
    SymmetricAlg.functor Y ⋙ pullback f ⟶ pullback f ⋙ SymmetricAlg.functor X where
  app F := comparison f F
  naturality := fun {F G} g ↦ comparison_naturality f (F := F) (G := G) g

/-- Every component of the symmetric-algebra pullback natural transformation is invertible. -/
@[stacks 01CI "(3), symmetric-algebra pullback natural transformation is invertible"]
instance natTrans_isIso (f : X ⟶ Y) : IsIso (natTrans f) := sorry

/-- The symmetric-algebra pullback comparison isomorphism is natural in the module sheaf. -/
@[stacks 01CI "symmetric-algebra pullback comparison isomorphism naturality"]
theorem comparisonIso_naturality (f : X ⟶ Y) {F G : Y.Modules} (g : F ⟶ G) :
    (SymmetricAlg.functor Y ⋙ pullback f).map g ≫ (comparisonIso f G).hom =
      (comparisonIso f F).hom ≫
        (pullback f ⋙ SymmetricAlg.functor X).map g := sorry

/-- The named inverse comparisons are natural in the module sheaf. -/
@[stacks 01CI "symmetric-algebra inverse comparison naturality"]
theorem comparisonInv_naturality (f : X ⟶ Y) {F G : Y.Modules} (g : F ⟶ G) :
    (pullback f ⋙ SymmetricAlg.functor X).map g ≫ comparisonInv f G =
      comparisonInv f F ≫ (SymmetricAlg.functor Y ⋙ pullback f).map g := sorry

/-- The inverse components of the symmetric-algebra natural isomorphism form a named
  natural transformation. -/
@[stacks 01CI "symmetric-algebra inverse pullback natural transformation"]
noncomputable def invNatTrans (f : X ⟶ Y) :
    pullback f ⋙ SymmetricAlg.functor X ⟶ SymmetricAlg.functor Y ⋙ pullback f where
  app F := comparisonInv f F
  naturality := fun {F G} g ↦ comparisonInv_naturality f g

/-- The symmetric-algebra comparison and its inverse natural transformation compose to the identity. -/
@[simp, stacks 01CI "symmetric-algebra natural transformation forward-inverse law"]
theorem natTrans_hom_inv_id (f : X ⟶ Y) :
    natTrans f ≫ invNatTrans f = 𝟙 _ := sorry

/-- The inverse symmetric-algebra natural transformation and comparison compose to the identity. -/
@[simp, stacks 01CI "symmetric-algebra natural transformation inverse-forward law"]
theorem natTrans_inv_hom_id (f : X ⟶ Y) :
    invNatTrans f ≫ natTrans f = 𝟙 _ := sorry

/-- The symmetric-algebra pullback comparisons as a natural isomorphism. -/
@[stacks 01CI "symmetric-algebra pullback natural isomorphism"]
noncomputable def comparisonNatIso (f : X ⟶ Y) :
    SymmetricAlg.functor Y ⋙ pullback f ≅ pullback f ⋙ SymmetricAlg.functor X where
  hom := natTrans f
  inv := invNatTrans f
  hom_inv_id := natTrans_hom_inv_id f
  inv_hom_id := natTrans_inv_hom_id f

/-- A component of the symmetric-algebra pullback natural isomorphism. -/
@[simp, stacks 01CI "symmetric-algebra pullback natural isomorphism component"]
theorem comparisonNatIso_app (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonNatIso f).app F = comparisonIso f F := sorry

/-- The forward transformation of the symmetric-algebra pullback natural isomorphism. -/
@[simp, stacks 01CI "symmetric-algebra pullback natural isomorphism hom"]
theorem comparisonNatIso_hom (f : X ⟶ Y) :
    (comparisonNatIso f).hom = natTrans f := sorry

/-- The forward component of the symmetric-algebra pullback natural isomorphism. -/
@[simp, stacks 01CI "symmetric-algebra pullback natural isomorphism hom component"]
theorem comparisonNatIso_hom_app (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonNatIso f).hom.app F = comparison f F := sorry

/-- The inverse transformation of the symmetric-algebra natural isomorphism is `invNatTrans`. -/
@[simp, stacks 01CI "symmetric-algebra pullback natural isomorphism inverse"]
theorem comparisonNatIso_inv (f : X ⟶ Y) :
    (comparisonNatIso f).inv = invNatTrans f := sorry

/-- The inverse component of the symmetric-algebra pullback natural isomorphism. -/
@[simp, stacks 01CI "symmetric-algebra pullback natural isomorphism inverse component"]
theorem comparisonNatIso_inv_app (f : X ⟶ Y) (F : Y.Modules) :
    (comparisonNatIso f).inv.app F = comparisonInv f F := sorry

end AlgebraicGeometry.RingedSpace.SymmetricAlg.Pullback
