module

public import ReasLib.CategoryTheory.Sites.CategoryHomology.Bar
public import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Augmentation of the category-homology bar complex

The composable-arrow bar construction has a canonical augmentation to the colimit of its
coefficient presheaf.  This leaf keeps the two directions of the degree-zero comparison explicit:
the forward map is induced by the chain augmentation, while the inverse is induced by the
colimit cocone of degree-zero homology classes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology

noncomputable section

universe u v u' v' w

namespace CategoryTheory.CategoryHomology.Bar

variable {C : Type u} [Category.{v} C]
variable [UnivLE.{max u v, w}]

/-- The coefficient identity induces the identity simplicial bar map. -/
@[simp, stacks 08PG "simplicial bar coefficient identity"]
theorem simplicialMap_id_coeff (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    CategoryHomology.simplicialMap (𝟭 C) (𝟙 F) =
      𝟙 (CategoryHomology.simplicialObject F) := sorry

/-- Simplicial bar maps compose with coefficient morphisms. -/
@[simp, stacks 08PG "simplicial bar coefficient composition"]
theorem simplicialMap_comp_coeff
    {F G H : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (f : F ⟶ G) (g : G ⟶ H) :
    CategoryHomology.simplicialMap (𝟭 C) (f ≫ g) =
      CategoryHomology.simplicialMap (𝟭 C) f ≫
        CategoryHomology.simplicialMap (𝟭 C) g := sorry

/-- The simplicial bar construction as a functor of coefficient presheaves. -/
@[stacks 08PG "functorial simplicial bar construction"]
noncomputable def simplicialObjectFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ SimplicialObject AddCommGrpCat.{w} where
  obj F := CategoryHomology.simplicialObject F
  map t := CategoryHomology.simplicialMap (𝟭 C) t
  map_id := simplicialMap_id_coeff
  map_comp := simplicialMap_comp_coeff

/-- Evaluation of the simplicial bar functor on a coefficient presheaf. -/
@[simp, stacks 08PG "simplicial bar functor object formula"]
theorem simplicialObjectFunctor_obj (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (simplicialObjectFunctor (C := C)).obj F =
      CategoryHomology.simplicialObject F := sorry

/-- Evaluation of the simplicial bar functor on a coefficient morphism. -/
@[simp, stacks 08PG "simplicial bar functor map formula"]
theorem simplicialObjectFunctor_map
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (f : F ⟶ G) :
    (simplicialObjectFunctor (C := C)).map f =
      CategoryHomology.simplicialMap (𝟭 C) f := sorry

section Colimit

variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]

/-- Compatibility of the bar colimit maps with the simplicial operators. -/
@[stacks 08PG "bar colimit-cocone compatibility"]
theorem colimitAugmentationApp_naturality
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (CategoryHomology.simplicialObject F).map f ≫
        Sigma.desc (fun x : ComposableArrows C Δ'.unop.len ↦
          colimit.ι F (op x.right)) =
      Sigma.desc (fun x : ComposableArrows C Δ.unop.len ↦
          colimit.ι F (op x.right)) ≫
        ((SimplicialObject.const AddCommGrpCat.{w}).obj
          ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).obj F)).map f := sorry

/-- The canonical augmentation from the simplicial bar construction of `F` to the constant
simplicial object on `colim.obj F`. -/
@[stacks 08PG "bar simplicial colimit augmentation component"]
def colimitAugmentationApp (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    CategoryHomology.simplicialObject F ⟶
      (SimplicialObject.const AddCommGrpCat.{w}).obj
        ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).obj F) where
  app Δ := Sigma.desc (fun x : ComposableArrows C Δ.unop.len ↦
    colimit.ι F (op x.right))
  naturality _ _ f := colimitAugmentationApp_naturality F f

/-- Naturality of the bar colimit augmentation in the coefficient presheaf. -/
@[stacks 08PG "bar colimit augmentation coefficient naturality"]
theorem colimitAugmentation_naturality
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (t : F ⟶ G) :
    CategoryHomology.simplicialMap (𝟭 C) t ≫ colimitAugmentationApp G =
      colimitAugmentationApp F ≫
        (SimplicialObject.const AddCommGrpCat.{w}).map
          ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).map t) := sorry

/-- The canonical natural augmentation from the simplicial bar functor to the constant
simplicial object on the presheaf colimit. -/
@[stacks 08PG "canonical bar colimit augmentation"]
def colimitAugmentation :
    simplicialObjectFunctor (C := C) ⟶
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}) ⋙
        SimplicialObject.const AddCommGrpCat.{w} where
  app F := colimitAugmentationApp F
  naturality _ _ t := colimitAugmentation_naturality t

/-- The simplicial bar construction of one presheaf, bundled with its colimit augmentation. -/
@[stacks 08PG "augmented category-homology bar object"]
def augmentedObj (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    SimplicialObject.Augmented AddCommGrpCat.{w} where
  left := CategoryHomology.simplicialObject F
  right := (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).obj F
  hom := colimitAugmentationApp F

/-- The morphism of augmented bar constructions induced by a coefficient morphism. -/
@[stacks 08PG "augmented category-homology bar map"]
def augmentedMap {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (t : F ⟶ G) :
    augmentedObj F ⟶ augmentedObj G :=
  CommaMorphism.mk (CategoryHomology.simplicialMap (𝟭 C) t)
    ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).map t)
    (colimitAugmentation_naturality t)

/-- The augmented bar map attached to an identity is the identity. -/
@[stacks 08PG "augmented category-homology bar identity law"]
theorem augmentedMap_id (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    augmentedMap (𝟙 F) = 𝟙 _ := sorry

/-- Augmented bar maps preserve composition. -/
@[stacks 08PG "augmented category-homology bar composition law"]
theorem augmentedMap_comp
    {F G H : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (f : F ⟶ G) (g : G ⟶ H) :
    augmentedMap (f ≫ g) = augmentedMap f ≫ augmentedMap g := sorry

/-- The augmented category-homology bar construction, functorial in coefficients. -/
@[stacks 08PG "functorial augmented category-homology bar construction"]
def augmentedFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ SimplicialObject.Augmented AddCommGrpCat.{w} where
  obj F := augmentedObj F
  map t := augmentedMap t
  map_id F := augmentedMap_id F
  map_comp f g := augmentedMap_comp f g

/-- Forgetting the augmentation recovers the simplicial bar functor. -/
@[simp, stacks 08PG "augmented bar underlying simplicial functor"]
theorem augmentedFunctor_comp_drop :
    augmentedFunctor (C := C) ⋙ SimplicialObject.Augmented.drop =
      simplicialObjectFunctor (C := C) := sorry

/-- Taking augmentation points recovers the presheaf colimit functor. -/
@[simp, stacks 08PG "augmented bar point functor"]
theorem augmentedFunctor_comp_point :
    augmentedFunctor (C := C) ⋙ SimplicialObject.Augmented.point =
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}) := sorry

/-- The canonical chain augmentation from the bar complex to the presheaf colimit concentrated
in degree zero. -/
@[stacks 08PG "category-homology bar chain augmentation"]
def chainAugmentation :
    augmentedFunctor (C := C) ⋙ SimplicialObject.Augmented.drop ⋙
          alternatingFaceMapComplex AddCommGrpCat.{w} ⟶
      augmentedFunctor (C := C) ⋙ SimplicialObject.Augmented.point ⋙
          ChainComplex.single₀ AddCommGrpCat.{w} :=
  Functor.whiskerLeft (augmentedFunctor (C := C)) AlternatingFaceMapComplex.ε

/-- The canonical map from zeroth bar homology to the presheaf colimit. -/
@[stacks 08PG "zeroth bar homology to colimit"]
def zeroMap (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    homology (C := C) F 0 ⟶
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).obj F :=
  HomologicalComplex.homologyMap
      (AlternatingFaceMapComplex.ε.app (augmentedObj F)) 0 ≫
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 0
      ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).obj F)).hom

/-- The degree-zero class map from a coefficient value into zeroth bar homology. -/
@[stacks 08PG "coefficient value to zeroth bar homology"]
def zeroCoconeApp (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (U : Cᵒᵖ) :
    F.obj U ⟶ homology (C := C) F 0 :=
  Sigma.ι (fun x : ComposableArrows C 0 ↦ F.obj (op x.right))
      (ComposableArrows.mk₀ U.unop) ≫
    (CategoryHomology.complex F).pOpcycles 0 ≫
      (ChainComplex.isoHomologyι₀ (CategoryHomology.complex F)).inv

/-- The degree-zero class maps form a cocone on the coefficient presheaf. -/
@[stacks 08PG "zeroth bar homology cocone compatibility"]
theorem zeroCoconeApp_naturality
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) {U V : Cᵒᵖ} (f : U ⟶ V) :
    F.map f ≫ zeroCoconeApp F V = zeroCoconeApp F U := sorry

/-- Zeroth bar homology as a cocone under the coefficient presheaf. -/
@[stacks 08PG "zeroth bar homology colimit cocone"]
def zeroCocone (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) : Cocone F where
  pt := homology (C := C) F 0
  ι :=
    { app := zeroCoconeApp F
      naturality := fun _ _ f ↦ zeroCoconeApp_naturality F f }

/-- The canonical map from the presheaf colimit to zeroth bar homology. -/
@[stacks 08PG "colimit to zeroth bar homology"]
def zeroInverse (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).obj F ⟶
      homology (C := C) F 0 :=
  colimit.desc F (zeroCocone F)

/-- Naturality of the map from zeroth bar homology to colimit. -/
@[stacks 08PG "zeroth bar homology to colimit naturality"]
theorem zeroMap_naturality
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (t : F ⟶ G) :
    map (C := C) (C' := C) (𝟭 C) t 0 ≫ zeroMap G =
      zeroMap F ≫
        (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).map t := sorry

/-- Naturality of the map from colimit to zeroth bar homology. -/
@[stacks 08PG "colimit to zeroth bar homology naturality"]
theorem zeroInverse_naturality
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (t : F ⟶ G) :
    (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).map t ≫ zeroInverse G =
      zeroInverse F ≫ map (C := C) (C' := C) (𝟭 C) t 0 := sorry

/-- The natural transformation from zeroth bar homology to presheaf colimit. -/
@[stacks 08PG "zeroth bar homology to colimit natural transformation"]
def zeroNatTrans :
    coefficientFunctor (C := C) 0 ⟶
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}) where
  app F := zeroMap F
  naturality _ _ t := zeroMap_naturality t

/-- The natural transformation from presheaf colimit to zeroth bar homology. -/
@[stacks 08PG "colimit to zeroth bar homology natural transformation"]
def zeroInverseNatTrans :
    (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}) ⟶
      coefficientFunctor (C := C) 0 where
  app F := zeroInverse F
  naturality _ _ t := zeroInverse_naturality t

/-- The bar-to-colimit transformation followed by its explicit inverse is the identity. -/
@[stacks 08PG "zeroth bar homology comparison forward-inverse law"]
theorem zeroNatTrans_hom_inv_id :
    zeroNatTrans (C := C) ≫ zeroInverseNatTrans (C := C) = 𝟙 _ := sorry

/-- The explicit inverse followed by the bar-to-colimit transformation is the identity. -/
@[stacks 08PG "zeroth bar homology comparison inverse-forward law"]
theorem zeroNatTrans_inv_hom_id :
    zeroInverseNatTrans (C := C) ≫ zeroNatTrans (C := C) = 𝟙 _ := sorry

/-- The canonical natural isomorphism from zeroth bar homology to presheaf colimit.  Both
directions are explicit; no isomorphism is selected from an `IsIsomorphic` proposition. -/
@[stacks 08PG "zeroth bar homology is presheaf colimit"]
def zeroIso :
    coefficientFunctor (C := C) 0 ≅
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}) where
  hom := zeroNatTrans
  inv := zeroInverseNatTrans
  hom_inv_id := zeroNatTrans_hom_inv_id
  inv_hom_id := zeroNatTrans_inv_hom_id

/-- The forward component of `zeroIso` is induced by the chain augmentation. -/
@[simp, stacks 08PG "zeroth bar homology comparison forward component"]
theorem zeroIso_hom_app (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (zeroIso (C := C)).hom.app F = zeroMap F := sorry

/-- The inverse component of `zeroIso` is induced by the explicit degree-zero cocone. -/
@[simp, stacks 08PG "zeroth bar homology comparison inverse component"]
theorem zeroIso_inv_app (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (zeroIso (C := C)).inv.app F = zeroInverse F := sorry

end Colimit

section ChangeOfIndex

variable {C' : Type u'} [Category.{v'} C']
variable [UnivLE.{max u' v', w}]
variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]
variable [HasColimitsOfShape C'ᵒᵖ AddCommGrpCat.{w}]

/-- The colimit map induced by a functor of indexing categories and a compatible coefficient
morphism. -/
@[stacks 08PH "colimit map induced by an indexing functor"]
def colimitMap (u : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : F' ⟶ u.op ⋙ F) :
    (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).obj F' ⟶
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).obj F :=
  (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).map t ≫
    colimit.pre F u.op

/-- The explicit simplicial bar map commutes with the colimit augmentations. -/
@[stacks 08PH "bar map and colimit augmentation compatibility"]
theorem colimitAugmentation_map (u : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : F' ⟶ u.op ⋙ F) :
    CategoryHomology.simplicialMap u t ≫ colimitAugmentationApp (C := C) F =
      colimitAugmentationApp (C := C') F' ≫
        (SimplicialObject.const AddCommGrpCat.{w}).map (colimitMap u t) := sorry

/-- The morphism of augmented bar constructions induced by a functor of indexing categories and
a compatible coefficient morphism. -/
@[stacks 08PH "augmented bar map induced by an indexing functor"]
def augmentedMapOfFunctor (u : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : F' ⟶ u.op ⋙ F) :
    augmentedObj (C := C') F' ⟶ augmentedObj (C := C) F :=
  CommaMorphism.mk (CategoryHomology.simplicialMap u t) (colimitMap u t)
    (colimitAugmentation_map u t)

/-- The explicit bar-complex map commutes with the chain augmentations. -/
@[stacks 08PH "bar complex map and chain augmentation compatibility"]
theorem chainAugmentation_map (u : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : F' ⟶ u.op ⋙ F) :
    CategoryHomology.complexMap u t ≫
        AlternatingFaceMapComplex.ε.app (augmentedObj (C := C) F) =
      AlternatingFaceMapComplex.ε.app (augmentedObj (C := C') F') ≫
        (ChainComplex.single₀ AddCommGrpCat.{w}).map (colimitMap u t) := sorry

/-- The degree-zero bar-homology map commutes with the canonical maps to colimits. -/
@[stacks 08PH "zeroth bar homology map and colimit compatibility"]
theorem zeroMap_map (u : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : F' ⟶ u.op ⋙ F) :
    CategoryHomology.Bar.map u t 0 ≫ zeroMap (C := C) F =
      zeroMap (C := C') F' ≫ colimitMap u t := sorry

/-- The inverse degree-zero comparison also commutes with change of indexing category. -/
@[stacks 08PH "colimit map and inverse zeroth-homology compatibility"]
theorem zeroInverse_map (u : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{w}}
    (t : F' ⟶ u.op ⋙ F) :
    colimitMap u t ≫ zeroInverse (C := C) F =
      zeroInverse (C := C') F' ≫ CategoryHomology.Bar.map u t 0 := sorry

end ChangeOfIndex

end CategoryTheory.CategoryHomology.Bar
