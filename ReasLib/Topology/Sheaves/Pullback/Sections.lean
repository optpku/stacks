/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Stalks.Pullback
public import ReasLib.Topology.Sheaves.Pullback.Composition

/-!
# Sections of pullback sheaves

This file packages the rule sending an arrow `f : Y ⟶ X` to the sections of `f⁻¹ G` over the
inverse image of a fixed open of `X`.  The construction is functorial on an over category and is
independent of any site topology or inverse-limit hypothesis.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u v w

namespace TopCat.Sheaf.PullbackSections

variable {C : Type (w + 1)} [Category.{w} C]
variable {FC : C → C → Type w} {CC : C → Type w}
variable [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{w} C FC]
variable [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]

/-- The canonical map on sections induced by pulling back first along `g` and then along `f`. -/
noncomputable def iteratedMap {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Z.Sheaf C) (U : Opens Z) :
    ((((g⁻¹).obj G).presheaf).obj (op ((Opens.map g).obj U))) ⟶
      ((((f ≫ g)⁻¹).obj G).presheaf).obj (op ((Opens.map (f ≫ g)).obj U)) :=
  (((pullbackPushforwardAdjunction C f).unit.app ((g⁻¹).obj G)).1.app
      (op ((Opens.map g).obj U))) ≫
    ((pullbackComp (A := C) f g).hom.app G).1.app
      (op ((Opens.map f).obj ((Opens.map g).obj U))) ≫
    eqToHom (congrArg
      (fun V : Opens X ↦ ((((f ≫ g)⁻¹).obj G).presheaf).obj (op V))
      (Opens.map_comp_obj f g U).symm)

/-- The transition map on pullback sections along a morphism in an over category. -/
noncomputable def overMap {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{w}) {i : I}
    (G : (F.obj i).Sheaf C) (U : Opens (F.obj i)) {A B : Over i} (φ : A ⟶ B) :
    ((((F.map B.hom)⁻¹).obj G).presheaf).obj
        (op ((Opens.map (F.map B.hom)).obj U)) ⟶
      ((((F.map A.hom)⁻¹).obj G).presheaf).obj
        (op ((Opens.map (F.map A.hom)).obj U)) :=
  iteratedMap (F.map φ.left) (F.map B.hom) G U ≫
    eqToHom (congrArg
      (fun k : F.obj A.left ⟶ F.obj i ↦
        ((((k⁻¹).obj G).presheaf).obj (op ((Opens.map k).obj U))))
      ((F.map_comp φ.left B.hom).symm.trans
        (congrArg (fun k ↦ F.map k) (Over.w φ))))

/-- Identity compatibility for the transition maps of pullback sections. -/
theorem overMap_id {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{w}) {i : I}
    (G : (F.obj i).Sheaf C) (U : Opens (F.obj i)) (A : Over i) :
    overMap F G U (𝟙 A) = 𝟙 _ := sorry

/-- Composition compatibility for the transition maps of pullback sections. -/
theorem overMap_comp {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{w}) {i : I}
    (G : (F.obj i).Sheaf C) (U : Opens (F.obj i))
    {A B D : Over i} (φ : A ⟶ B) (ψ : B ⟶ D) :
    overMap F G U (φ ≫ ψ) = overMap F G U ψ ≫ overMap F G U φ := sorry

/-- The presheaf on `Over i` sending `a : j ⟶ i` to sections of `(F.map a)⁻¹ G` over the
inverse image of `U`. -/
@[stacks 09X3 "pullback-section presheaf"]
noncomputable def over {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{w}) (i : I)
    (G : (F.obj i).Sheaf C) (U : Opens (F.obj i)) : (Over i)ᵒᵖ ⥤ C where
  obj A := ((((F.map A.unop.hom)⁻¹).obj G).presheaf).obj
    (op ((Opens.map (F.map A.unop.hom)).obj U))
  map φ := overMap F G U φ.unop
  map_id A := overMap_id F G U A.unop
  map_comp φ ψ := overMap_comp F G U ψ.unop φ.unop

/-- The componentwise action of a sheaf morphism on pullback sections. -/
noncomputable def mapApp {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{w}) {i : I}
    {G H : (F.obj i).Sheaf C} (U : Opens (F.obj i)) (f : G ⟶ H) (A : Over i) :
    (over F i G U).obj (op A) ⟶ (over F i H U).obj (op A) :=
  (((F.map A.hom)⁻¹).map f).1.app (op ((Opens.map (F.map A.hom)).obj U))

/-- The action of a sheaf morphism commutes with transition maps on the over category. -/
theorem mapApp_naturality {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{w}) {i : I}
    {G H : (F.obj i).Sheaf C} (U : Opens (F.obj i)) (f : G ⟶ H)
    {A B : (Over i)ᵒᵖ} (φ : A ⟶ B) :
    (over F i G U).map φ ≫ mapApp F U f B.unop =
      mapApp F U f A.unop ≫ (over F i H U).map φ := sorry

/-- A sheaf morphism induces a natural transformation between its pullback-section
presheaves. -/
noncomputable def map {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{w}) {i : I}
    {G H : (F.obj i).Sheaf C} (U : Opens (F.obj i)) (f : G ⟶ H) :
    over F i G U ⟶ over F i H U where
  app A := mapApp F U f A.unop
  naturality _ _ φ := mapApp_naturality F U f φ

/-- Identity compatibility for the action on the sheaf variable. -/
theorem map_id {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{w}) {i : I}
    (G : (F.obj i).Sheaf C) (U : Opens (F.obj i)) :
    map F U (𝟙 G) = 𝟙 (over F i G U) := sorry

/-- Composition compatibility for the action on the sheaf variable. -/
theorem map_comp {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{w}) {i : I}
    {G H K : (F.obj i).Sheaf C} (U : Opens (F.obj i)) (f : G ⟶ H) (g : H ⟶ K) :
    map F U (f ≫ g) = map F U f ≫ map F U g := sorry

/-- Pullback sections over a fixed open, functorial in the source sheaf. -/
@[stacks 09X3 "pullback-section functor"]
noncomputable def functor {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{w}) (i : I)
    (U : Opens (F.obj i)) : (F.obj i).Sheaf C ⥤ (Over i)ᵒᵖ ⥤ C where
  obj G := over F i G U
  map f := map F U f
  map_id G := map_id F G U
  map_comp f g := map_comp F U f g

end TopCat.Sheaf.PullbackSections
