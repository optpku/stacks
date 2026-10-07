module
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Topology.Sheaves.Functors
public import stacks_project.Chap85.Lemma_85_2_1_Site

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

/-- Restriction is the existing continuous direct image along the degree fiber. -/
abbrev fiberRestriction (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    [(DiagramOpens.fiber X n).IsContinuous
      (Opens.grothendieckTopology (X.obj n)) (zariskiTopology X)] :=
  (DiagramOpens.fiber X n).sheafPushforwardContinuous (Type u)
    (Opens.grothendieckTopology (X.obj n)) (zariskiTopology X)

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

/-- Explicit product presheaf giving right extension from a degree. -/
def fiberRightPresheaf (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (G : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u)) :
    (zariskiSite X)ᵒᵖ ⥤ Type u where
  obj U := (a : n ⟶ U.unop.base) → G.obj.obj (op (fiberOpen X n U.unop a))
  map {U V} g := TypeCat.ofHom fun s a =>
    G.obj.map (homOfLE (fiberOpen_le X n g.unop a)).op (s (a ≫ g.unop.base))
  map_id := sorry
  map_comp := sorry

/-- The product presheaf is a sheaf for the fixed-degree open-cover topology. -/
theorem fiberRightPresheaf_isSheaf (X : SimplicialObject TopCat.{u})
    (n : SimplexCategoryᵒᵖ) (G : Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u)) :
    Presheaf.IsSheaf (zariskiTopology X) (fiberRightPresheaf X n G) := sorry

/-- Right extension applies a sheaf morphism to each indexed section. -/
def fiberRight (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    Sheaf (Opens.grothendieckTopology (X.obj n)) (Type u) ⥤ Sheaf (zariskiTopology X) (Type u) where
  obj G := ⟨fiberRightPresheaf X n G, fiberRightPresheaf_isSheaf X n G⟩
  map h := ⟨{ app := fun U => TypeCat.ofHom fun s a => h.hom.app _ (s a)
              naturality := sorry }⟩
  map_id := sorry
  map_comp := sorry

/-- The identity-stage inverse-image open agrees with the original open. -/
theorem fiberOpen_id (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (U : Opens (X.obj n)) :
    fiberOpen X n ((DiagramOpens.fiber X n).obj U) (𝟙 n) = U := by
  change (Opens.map (X.map (𝟙 n))).obj U = U
  rw [X.map_id, Opens.map_id_obj]

variable (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
variable [(DiagramOpens.fiber X n).IsContinuous
  (Opens.grothendieckTopology (X.obj n)) (zariskiTopology X)]

/-- Unit: restrict a section along each actual inverse-image diagram arrow. -/
def fiberRightUnit : 𝟭 _ ⟶ fiberRestriction X n ⋙ fiberRight X n where
  app F := ⟨{ app := fun U => TypeCat.ofHom fun s a => F.obj.map (fiberOpenLift X n U.unop a).op s
              naturality := sorry }⟩
  naturality := sorry

/-- Counit: evaluate the identity-arrow factor and restrict along the proven identity-open equality. -/
def fiberRightCounit : fiberRight X n ⋙ fiberRestriction X n ⟶ 𝟭 _ where
  app G := ⟨{ app := fun U =>
                TypeCat.ofHom fun s => G.obj.map (eqToHom (fiberOpen_id X n U.unop).symm).op (s (𝟙 n))
              naturality := sorry }⟩
  naturality := sorry

/-- Restriction is left adjoint to the explicit product right extension. -/
def fiberRestrictionRightAdjunction : fiberRestriction X n ⊣ fiberRight X n where
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
  right_triangle_components := sorry

end CategoryTheory.SimplicialObject
