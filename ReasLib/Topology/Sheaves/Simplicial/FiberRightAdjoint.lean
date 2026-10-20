module
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.Topology.Category.TopCat.DiagramOpens.Component

/-!
# Right extension from one degree of the diagram-open site

At `(i,U)` the right extension is the product over arrows `n ⟶ i` of
sections on the inverse image of `U`. Covers have fixed degree, so each
factor satisfies the ordinary open-cover sheaf condition.
-/
@[expose] public section
open CategoryTheory TopologicalSpace TopCat Opposite
noncomputable section
universe u
namespace CategoryTheory.SimplicialObject

/-- Inverse image of a diagram open along a fixed base arrow. -/
def fiberOpen (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (U : DiagramOpens X) (a : n ⟶ U.base) : Opens (X.obj n) :=
  (Opens.map (X.map a)).obj U.opens

/-- The canonical arrow from an inverse-image open to its diagram open. -/
def fiberOpenLift (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (U : DiagramOpens X) (a : n ⟶ U.base) :
    (DiagramOpens.fiber X n).obj (fiberOpen X n U a) ⟶ U :=
  DiagramOpens.homMk a (fun _ h => h)

/-- An arrow of diagram opens induces the corresponding containment of inverse images. -/
theorem fiberOpen_le (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    {U V : DiagramOpens X} (g : U ⟶ V) (a : n ⟶ U.base) :
    fiberOpen X n U a ≤ fiberOpen X n V (a ≫ g.base) := by
  intro x hx
  change (X.map (a ≫ g.base)).hom x ∈ V.opens
  rw [X.map_comp]
  exact g.mapsTo hx

/-- The product of sections indexed by arrows from a fixed degree. -/
def fiberRightSections (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (G : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u))
    (U : (zariskiSite X)ᵒᵖ) : Type u :=
  (arrow : n ⟶ U.unop.base) → G.obj.obj (op (fiberOpen X n U.unop arrow))

/-- Restriction of indexed sections along a diagram-open arrow. -/
def fiberRightSectionsMap (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (G : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u))
    {U V : (zariskiSite X)ᵒᵖ} (morphism : U ⟶ V) :
    fiberRightSections X n G U ⟶ fiberRightSections X n G V :=
  TypeCat.ofHom fun sections arrow =>
    G.obj.map (homOfLE (fiberOpen_le X n morphism.unop arrow)).op
      (sections (arrow ≫ morphism.unop.base))

/-- Restriction of indexed sections along an identity is the identity. -/
theorem fiberRightPresheaf_map_id (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (G : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u))
    (U : (zariskiSite X)ᵒᵖ) :
    fiberRightSectionsMap X n G (𝟙 U) = 𝟙 (fiberRightSections X n G U) := sorry

/-- Restriction of indexed sections respects composition. -/
theorem fiberRightPresheaf_map_comp (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (G : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u))
    {U V W : (zariskiSite X)ᵒᵖ} (first : U ⟶ V) (second : V ⟶ W) :
    fiberRightSectionsMap X n G (first ≫ second) =
      fiberRightSectionsMap X n G first ≫ fiberRightSectionsMap X n G second := sorry

/-- The product presheaf giving right extension from a degree. -/
def fiberRightPresheaf (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (G : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u)) :
    (zariskiSite X)ᵒᵖ ⥤ Type u where
  obj := fiberRightSections X n G
  map := fiberRightSectionsMap X n G
  map_id := fiberRightPresheaf_map_id X n G
  map_comp := fiberRightPresheaf_map_comp X n G

/-- The product presheaf is a sheaf for the fixed-degree open-cover topology. -/
theorem fiberRightPresheaf_isSheaf (X : SimplicialObject TopCat.{u})
    (n : SimplexCategoryᵒᵖ) (G : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u)) :
    Presheaf.IsSheaf (zariskiTopology X) (fiberRightPresheaf X n G) := sorry

/-- A sheaf morphism acts on each indexed section. -/
def fiberRightMapApp (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    {G H : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u)} (morphism : G ⟶ H)
    (U : (zariskiSite X)ᵒᵖ) :
    (fiberRightPresheaf X n G).obj U ⟶ (fiberRightPresheaf X n H).obj U :=
  TypeCat.ofHom fun sections arrow => morphism.hom.app _ (sections arrow)

/-- The action of a sheaf morphism on indexed sections is natural in diagram opens. -/
theorem fiberRight_map_naturality (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    {G H : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u)} (morphism : G ⟶ H)
    {U V : (zariskiSite X)ᵒᵖ} (restriction : U ⟶ V) :
    (fiberRightPresheaf X n G).map restriction ≫ fiberRightMapApp X n morphism V =
      fiberRightMapApp X n morphism U ≫ (fiberRightPresheaf X n H).map restriction := sorry

/-- The induced morphism of product-extension sheaves. -/
def fiberRightMap (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    {G H : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u)} (morphism : G ⟶ H) :
    (⟨fiberRightPresheaf X n G, fiberRightPresheaf_isSheaf X n G⟩ :
      Sheaf (zariskiTopology X) (Type u)) ⟶
    ⟨fiberRightPresheaf X n H, fiberRightPresheaf_isSheaf X n H⟩ :=
  ⟨{ app := fiberRightMapApp X n morphism
     naturality := fun _ _ restriction => fiberRight_map_naturality X n morphism restriction }⟩

/-- Product right extension sends identity sheaf morphisms to identities. -/
theorem fiberRight_map_id (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (G : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u)) :
    fiberRightMap X n (𝟙 G) = 𝟙 _ := sorry

/-- Product right extension preserves composition of sheaf morphisms. -/
theorem fiberRight_map_comp (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    {G H K : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u)}
    (first : G ⟶ H) (second : H ⟶ K) :
    fiberRightMap X n (first ≫ second) =
      fiberRightMap X n first ≫ fiberRightMap X n second := sorry

/-- Right extension applies a sheaf morphism to each indexed section. -/
def fiberRight (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u) ⥤ Sheaf (zariskiTopology X) (Type u) where
  obj G := ⟨fiberRightPresheaf X n G, fiberRightPresheaf_isSheaf X n G⟩
  map := fiberRightMap X n
  map_id := fiberRight_map_id X n
  map_comp := fiberRight_map_comp X n

/-- The identity-stage inverse-image open agrees with the original open. -/
theorem fiberOpen_id (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (U : Opens (X.obj n)) :
    fiberOpen X n ((DiagramOpens.fiber X n).obj U) (𝟙 n) = U := by
  change (Opens.map (X.map (𝟙 n))).obj U = U
  rw [X.map_id, Opens.map_id_obj]

variable (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)

/-- Restriction of a section along each inverse-image diagram arrow. -/
def fiberRightUnitAppMap (F : Sheaf (zariskiTopology X) (Type u))
    (U : (zariskiSite X)ᵒᵖ) :
    F.obj.obj U ⟶ ((sheafFiber X n (Type u) ⋙ fiberRight X n).obj F).obj.obj U :=
  TypeCat.ofHom fun sections arrow => F.obj.map (fiberOpenLift X n U.unop arrow).op sections

/-- Restriction along inverse-image arrows is natural in diagram opens. -/
theorem fiberRightUnit_app_naturality (F : Sheaf (zariskiTopology X) (Type u))
    {U V : (zariskiSite X)ᵒᵖ} (morphism : U ⟶ V) :
    F.obj.map morphism ≫ fiberRightUnitAppMap X n F V =
      fiberRightUnitAppMap X n F U ≫
        ((sheafFiber X n (Type u) ⋙ fiberRight X n).obj F).obj.map morphism := sorry

/-- The sheaf map restricting sections to all inverse-image factors. -/
def fiberRightUnitApp (F : Sheaf (zariskiTopology X) (Type u)) :
    F ⟶ (sheafFiber X n (Type u) ⋙ fiberRight X n).obj F :=
  ⟨{ app := fiberRightUnitAppMap X n F
     naturality := fun _ _ morphism => fiberRightUnit_app_naturality X n F morphism }⟩

/-- Restriction to all inverse-image factors is natural in sheaves. -/
theorem fiberRightUnit_naturality {F G : Sheaf (zariskiTopology X) (Type u)}
    (morphism : F ⟶ G) :
    morphism ≫ fiberRightUnitApp X n G =
      fiberRightUnitApp X n F ≫ (sheafFiber X n (Type u) ⋙ fiberRight X n).map morphism := sorry

/-- The unit restricts a section along each inverse-image diagram arrow. -/
def fiberRightUnit : 𝟭 _ ⟶ sheafFiber X n (Type u) ⋙ fiberRight X n where
  app := fiberRightUnitApp X n
  naturality := fun _ _ morphism => fiberRightUnit_naturality X n morphism

/-- Evaluation at the identity-arrow factor, transported to the original open. -/
def fiberRightCounitAppMap
    (G : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u))
    (U : (Opens (X.obj n))ᵒᵖ) :
    ((fiberRight X n ⋙ sheafFiber X n (Type u)).obj G).obj.obj U ⟶ G.obj.obj U :=
  TypeCat.ofHom fun sections =>
    G.obj.map (eqToHom (fiberOpen_id X n U.unop).symm).op (sections (𝟙 n))

/-- Evaluation of the identity-arrow factor is natural in opens. -/
theorem fiberRightCounit_app_naturality
    (G : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u))
    {U V : (Opens (X.obj n))ᵒᵖ} (morphism : U ⟶ V) :
    ((fiberRight X n ⋙ sheafFiber X n (Type u)).obj G).obj.map morphism ≫
        fiberRightCounitAppMap X n G V =
      fiberRightCounitAppMap X n G U ≫ G.obj.map morphism := sorry

/-- The sheaf map evaluating the identity-arrow factor. -/
def fiberRightCounitApp
    (G : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u)) :
    (fiberRight X n ⋙ sheafFiber X n (Type u)).obj G ⟶ G :=
  ⟨{ app := fiberRightCounitAppMap X n G
     naturality := fun _ _ morphism => fiberRightCounit_app_naturality X n G morphism }⟩

/-- Evaluation of the identity-arrow factor is natural in sheaves. -/
theorem fiberRightCounit_naturality
    {G H : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u)} (morphism : G ⟶ H) :
    (fiberRight X n ⋙ sheafFiber X n (Type u)).map morphism ≫ fiberRightCounitApp X n H =
      fiberRightCounitApp X n G ≫ morphism := sorry

/-- The counit evaluates the identity-arrow factor at the original open. -/
def fiberRightCounit : fiberRight X n ⋙ sheafFiber X n (Type u) ⟶ 𝟭 _ where
  app := fiberRightCounitApp X n
  naturality := fun _ _ morphism => fiberRightCounit_naturality X n morphism

/-- The unit and counit satisfy the triangle identity on product right extensions. -/
theorem sheafFiberRightAdjunction_right_triangle
    (G : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u)) :
    (fiberRightUnit X n).app ((fiberRight X n).obj G) ≫
      (fiberRight X n).map ((fiberRightCounit X n).app G) = 𝟙 ((fiberRight X n).obj G) := sorry

/-- Degree restriction `sheafFiber` is left adjoint to the explicit product right extension. -/
def sheafFiberRightAdjunction : sheafFiber X n (Type u) ⊣ fiberRight X n where
  unit := fiberRightUnit X n
  counit := fiberRightCounit X n
  left_triangle_components F := by
    ext U s
    change F.obj.map ((DiagramOpens.fiber X n).map
        (eqToHom (fiberOpen_id X n U.unop).symm)).op
      (F.obj.map (fiberOpenLift X n ((DiagramOpens.fiber X n).obj U.unop) (𝟙 n)).op s) = s
    rw [← types_comp_apply, ← F.obj.map_comp, ← op_comp]
    have h : (DiagramOpens.fiber X n).map (eqToHom (fiberOpen_id X n U.unop).symm) ≫
        fiberOpenLift X n ((DiagramOpens.fiber X n).obj U.unop) (𝟙 n) =
        𝟙 ((DiagramOpens.fiber X n).obj U.unop) := by
      apply DiagramOpens.Hom.ext
      change 𝟙 n ≫ 𝟙 n = 𝟙 n
      simp
    rw [h, op_id, F.obj.map_id]
    rfl
  right_triangle_components := sheafFiberRightAdjunction_right_triangle X n

end CategoryTheory.SimplicialObject
