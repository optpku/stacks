module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Zariski site of a simplicial space

The site `X_Zar` associated to a simplicial topological space `X`: objects are opens of some
`X.obj (op n)`, morphisms are simplex operators `φ` with `X(φ)(U) ⊆ V`, and coverings are
identity-simplex open covers.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialObject

variable (X : SimplicialObject TopCat.{u})

/-- An object of the Zariski site of a simplicial space: an open subset of `X.obj (op n)`
for some simplex `n`. -/
structure ZariskiSite where
  /-- The simplex indexing the stage `X.obj (op simplex)` containing the open. -/
  simplex : SimplexCategory
  /-- An open subset of `X.obj (op simplex)`. -/
  opens : Opens (X.obj (op simplex))

namespace ZariskiSite

variable {X}

/-- An object of `ZariskiSite X` from a simplex and an open of the corresponding stage. -/
def of (n : SimplexCategory) (U : Opens (X.obj (op n))) : ZariskiSite X where
  simplex := n
  opens := U

/-- A morphism `U ⟶ V` in `ZariskiSite X` is a simplex operator
`φ : V.simplex ⟶ U.simplex` such that `U.opens ≤ (Opens.map (X.map φ.op)).obj V.opens`,
i.e. `X(φ)(U) ⊆ V`. -/
structure Hom (U V : ZariskiSite X) where
  /-- The underlying simplex operator `φ : V.simplex ⟶ U.simplex`. -/
  simplex : V.simplex ⟶ U.simplex
  /-- The containment `X(φ)(U) ⊆ V`. -/
  opens_le : U.opens ≤ (Opens.map (X.map simplex.op)).obj V.opens

/-- Build a morphism of `ZariskiSite X` from a simplex operator and the open-containment witness. -/
def homMk {U V : ZariskiSite X} (simplex : V.simplex ⟶ U.simplex)
    (opens_le : U.opens ≤ (Opens.map (X.map simplex.op)).obj V.opens) : Hom U V where
  simplex := simplex
  opens_le := opens_le

/-- The identity morphism of an object of `ZariskiSite X`, given by `𝟙` on the simplex. -/
def Hom.id (U : ZariskiSite X) : Hom U U where
  simplex := 𝟙 U.simplex
  opens_le := sorry

/-- Composition of morphisms of `ZariskiSite X` composes the simplex operators. -/
def Hom.comp {U V W : ZariskiSite X} (f : Hom U V) (g : Hom V W) : Hom U W where
  simplex := g.simplex ≫ f.simplex
  opens_le := sorry

/-- The simplex operator of `homMk simplex opens_le` is `simplex`. -/
theorem homMk_simplex {U V : ZariskiSite X} (simplex : V.simplex ⟶ U.simplex)
    (opens_le : U.opens ≤ (Opens.map (X.map simplex.op)).obj V.opens) :
    (homMk simplex opens_le).simplex = simplex := sorry

/-- Identity-simplex inclusions of opens of the same stage, as morphisms of `ZariskiSite X`. -/
def homOfLE {n : SimplexCategory} {U V : Opens (X.obj (op n))} (h : U ≤ V) :
    Hom (of n U) (of n V) :=
  homMk (𝟙 n) sorry

/-- The category of opens of the stages of `X`, with morphisms the compatible simplex operators. -/
@[reducible] def category : Category (ZariskiSite X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end ZariskiSite

/-- The bundled category of objects and morphisms in the simplicial Zariski site. -/
def zariskiSite : Cat where
  α := ZariskiSite X
  str := ZariskiSite.category

/-- The functor sending an ordinary open of `X.obj (op n)` to the corresponding object of
`ZariskiSite X` on the identity simplex `n`. -/
def ofOpens (n : SimplexCategory) : Opens (X.obj (op n)) ⥤ zariskiSite X where
  obj U := ZariskiSite.of n U
  map i := ZariskiSite.homOfLE i.le
  map_id := sorry
  map_comp := sorry

/-- `ofOpens n` sends `U` to the object with simplex `n` and open `U`. -/
theorem ofOpens_obj (n : SimplexCategory) (U : Opens (X.obj (op n))) :
    (ofOpens X n).obj U = ZariskiSite.of n U := sorry

/-- The morphism `X(φ)⁻¹(V) ⟶ V` in `ZariskiSite X` attached to `f : n ⟶ m`. -/
def pullbackHom {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (V : Opens (X.obj m)) :
    (zariskiSite X).str.Hom
      (ZariskiSite.of n.unop ((Opens.map (X.map f)).obj V))
      (ZariskiSite.of m.unop V) :=
  ZariskiSite.homMk f.unop le_rfl

/-- The simplex operator of `pullbackHom f V` is `f.unop`. -/
theorem pullbackHom_simplex {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (V : Opens (X.obj m)) :
    (pullbackHom X f V).simplex = f.unop := sorry

/-- A presieve in `X_Zar` is covering when it contains an identity-simplex open cover. -/
def zariskiPrecoverage : Precoverage (zariskiSite X) where
  coverings U := {R | ∀ x ∈ U.opens, ∃ (V : Opens (X.obj (op U.simplex))) (h : V ≤ U.opens),
    R (ZariskiSite.homOfLE h) ∧ x ∈ V}

/-- A sieve on `U` covers in `X_Zar` iff the identity-simplex arrows in the sieve cover `U`
as an open set. -/
def zariskiTopology : GrothendieckTopology (zariskiSite X) where
  sieves U := {S | ∀ x ∈ U.opens, ∃ (V : Opens (X.obj (op U.simplex))) (h : V ≤ U.opens),
    S (ZariskiSite.homOfLE h) ∧ x ∈ V}
  top_mem' := sorry
  pullback_stable' := sorry
  transitive' := sorry

/-- Membership in `zariskiTopology X` is the identity-simplex open-cover condition. -/
theorem mem_zariskiTopology_iff (U : zariskiSite X) (S : Sieve U) :
    S ∈ zariskiTopology X U ↔ ∀ x ∈ U.opens, ∃ (V : Opens (X.obj (op U.simplex))) (h : V ≤ U.opens),
      S (ZariskiSite.homOfLE h) ∧ x ∈ V := sorry

variable (C : Type v) [Category.{w} C]

/-- Restriction of a sheaf on `X_Zar` to the ordinary opens of the stage `X.obj (op n)`. -/
def restrictToDegree (n : SimplexCategory) :
    Sheaf (zariskiTopology X) C ⥤ (X.obj (op n)).Sheaf C where
  obj F := ⟨(ofOpens X n).op ⋙ F.obj, sorry⟩
  map {F G} α := ⟨{ app := fun V ↦ α.hom.app ((ofOpens X n).op.obj V), naturality := sorry }⟩
  map_id := sorry
  map_comp := sorry

/-- The underlying presheaf of `restrictToDegree n` is composition with `(ofOpens n).op`. -/
theorem restrictToDegree_obj (n : SimplexCategory) (F : Sheaf (zariskiTopology X) C) :
    ((restrictToDegree X C n).obj F).presheaf = (ofOpens X n).op ⋙ F.obj := sorry

end CategoryTheory.SimplicialObject
