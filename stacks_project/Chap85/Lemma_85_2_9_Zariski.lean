module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Topology.Category.TopCat.Opens
public import ReasLib.CategoryTheory.Functor.FreeAbelianYoneda

/-!
# Zariski category of a simplicial space

Objects of `Zariski X` are opens of some `X_n`. A morphism `U ⟶ V` is a simplex operator
`φ : V.simplex ⟶ U.simplex` such that `X(φ)` carries `U` into `V`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicTopology
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology.SimplicialSpace

/-- An object of the Zariski category of a simplicial topological space `X`: an open of some
`X.obj (op n)`. -/
structure Zariski (X : SimplicialObject TopCat.{u}) : Type u where
  /-- The simplex index `n` such that the open lives in `X_n`. -/
  simplex : SimplexCategory
  /-- The open subset of `X.obj (op simplex)`. -/
  opens : Opens (X.obj (op simplex))

namespace Zariski

/-- A morphism `U ⟶ V` in `Zariski X` is a simplex operator `φ : V.simplex ⟶ U.simplex`
with `X(φ)(U) ⊆ V`. -/
structure Hom {X : SimplicialObject TopCat.{u}} (U V : Zariski X) : Type where
  /-- The underlying simplex operator `φ : V.simplex ⟶ U.simplex`. -/
  simplex : V.simplex ⟶ U.simplex
  /-- The preimage condition `U.opens ≤ (Opens.map (X.map simplex.op)).obj V.opens`. -/
  le : U.opens ≤ (Opens.map (X.map simplex.op)).obj V.opens

/-- Build a morphism of `Zariski X` from a simplex operator and the preimage inclusion. -/
def homMk {X : SimplicialObject TopCat.{u}} {U V : Zariski X}
    (simplex : V.simplex ⟶ U.simplex)
    (le : U.opens ≤ (Opens.map (X.map simplex.op)).obj V.opens) : Hom U V where
  simplex := simplex
  le := le

/-- The identity simplex operator satisfies the preimage condition. -/
theorem Hom.id_le {X : SimplicialObject TopCat.{u}} (U : Zariski X) :
    U.opens ≤ (Opens.map (X.map (𝟙 U.simplex).op)).obj U.opens := sorry

/-- The identity morphism of an object of `Zariski X`. -/
def Hom.id {X : SimplicialObject TopCat.{u}} (U : Zariski X) : Hom U U :=
  homMk (𝟙 U.simplex) (Hom.id_le U)

/-- Composite simplex operators satisfy the preimage condition. -/
theorem Hom.comp_le {X : SimplicialObject TopCat.{u}} {U V W : Zariski X}
    (f : Hom U V) (g : Hom V W) :
    U.opens ≤ (Opens.map (X.map (g.simplex ≫ f.simplex).op)).obj W.opens := sorry

/-- Composition of morphisms of `Zariski X`. -/
def Hom.comp {X : SimplicialObject TopCat.{u}} {U V W : Zariski X}
    (f : Hom U V) (g : Hom V W) : Hom U W :=
  homMk (g.simplex ≫ f.simplex) (Hom.comp_le f g)

/-- Left identity for morphisms of `Zariski X`. -/
theorem Hom.id_comp {X : SimplicialObject TopCat.{u}} {U V : Zariski X} (f : Hom U V) :
    Hom.comp (Hom.id U) f = f := sorry

/-- Right identity for morphisms of `Zariski X`. -/
theorem Hom.comp_id {X : SimplicialObject TopCat.{u}} {U V : Zariski X} (f : Hom U V) :
    Hom.comp f (Hom.id V) = f := sorry

/-- Associativity for morphisms of `Zariski X`. -/
theorem Hom.assoc {X : SimplicialObject TopCat.{u}} {U V W Z : Zariski X}
    (f : Hom U V) (g : Hom V W) (h : Hom W Z) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := sorry

/-- The category of opens of the levels of a simplicial topological space. -/
instance category {X : SimplicialObject TopCat.{u}} : Category.{0} (Zariski X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The object of `Zariski X` given by an open of `X.obj (op n)`. -/
def of (X : SimplicialObject TopCat.{u}) (n : SimplexCategory)
    (U : Opens (X.obj (op n))) : Zariski X where
  simplex := n
  opens := U

/-- The simplex index of `of X n U` is `n`. -/
theorem of_simplex (X : SimplicialObject TopCat.{u}) (n : SimplexCategory)
    (U : Opens (X.obj (op n))) : (of X n U).simplex = n := sorry

/-- The open of `of X n U` is `U`. -/
theorem of_opens (X : SimplicialObject TopCat.{u}) (n : SimplexCategory)
    (U : Opens (X.obj (op n))) : (of X n U).opens = U := sorry

/-- The whole space `X_n` as an object of `Zariski X`. -/
def top (X : SimplicialObject TopCat.{u}) (n : SimplexCategory) : Zariski X where
  simplex := n
  opens := ⊤

/-- `top X n` is the whole space at simplex `n`. -/
theorem top_spec (X : SimplicialObject TopCat.{u}) (n : SimplexCategory) :
    (top X n).simplex = n ∧ (top X n).opens = ⊤ := sorry

/-- A simplex operator into a whole-space object automatically satisfies the preimage
condition, since the preimage of `⊤` is `⊤`. -/
theorem homMkTop_le {X : SimplicialObject TopCat.{u}} {U : Zariski X} {n : SimplexCategory}
    (φ : n ⟶ U.simplex) :
    U.opens ≤ (Opens.map (X.map φ.op)).obj (top X n).opens := sorry

/-- Build a morphism `U ⟶ top X n` from a simplex operator `n ⟶ U.simplex`. -/
def homMkTop {X : SimplicialObject TopCat.{u}} {U : Zariski X} {n : SimplexCategory}
    (φ : n ⟶ U.simplex) : Hom U (top X n) where
  simplex := φ
  le := homMkTop_le φ

/-- The simplex operator underlying a morphism of `Zariski X`. -/
def Hom.simplexMap {X : SimplicialObject TopCat.{u}} {U V : Zariski X} (f : U ⟶ V) :
    V.simplex ⟶ U.simplex :=
  (f : Hom U V).simplex

/-- The preimage condition of a morphism of `Zariski X`. -/
theorem Hom.opens_le {X : SimplicialObject TopCat.{u}} {U V : Zariski X} (f : U ⟶ V) :
    U.opens ≤ (Opens.map (X.map (Hom.simplexMap f).op)).obj V.opens := sorry

/-- The forward map of `hom_top_equiv` is inverted by `homMkTop`. -/
theorem hom_top_equiv_left_inv {X : SimplicialObject TopCat.{u}} (U : Zariski X)
    (n : SimplexCategory) (f : U ⟶ top X n) :
    homMkTop (Hom.simplexMap f) = f := sorry

/-- The reverse map of `hom_top_equiv` recovers the simplex operator. -/
theorem hom_top_equiv_right_inv {X : SimplicialObject TopCat.{u}} (U : Zariski X)
    (n : SimplexCategory) (φ : n ⟶ U.simplex) :
    Hom.simplexMap (homMkTop φ) = φ := sorry

/-- Morphisms into `top X n` are simplex operators `n ⟶ U.simplex`. -/
def hom_top_equiv {X : SimplicialObject TopCat.{u}} (U : Zariski X) (n : SimplexCategory) :
    (U ⟶ top X n) ≃ (n ⟶ U.simplex) where
  toFun := Hom.simplexMap
  invFun := homMkTop
  left_inv := hom_top_equiv_left_inv U n
  right_inv := hom_top_equiv_right_inv U n

/-- Face and degeneracy operators send whole spaces to whole spaces. -/
theorem spaceHom_le (X : SimplicialObject TopCat.{u}) {n m : SimplexCategory} (φ : m ⟶ n) :
    (top X n).opens ≤ (Opens.map (X.map φ.op)).obj (top X m).opens := sorry

/-- The morphism of whole spaces induced by a simplex operator. -/
def spaceHom (X : SimplicialObject TopCat.{u}) {n m : SimplexCategory} (φ : m ⟶ n) :
    Hom (top X n) (top X m) where
  simplex := φ
  le := spaceHom_le X φ

/-- Identity simplex operators induce identity morphisms of whole spaces. -/
theorem space_map_id (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    spaceHom X (𝟙 n).unop = Hom.id (top X n.unop) := sorry

/-- Composition of simplex operators induces composition of whole-space morphisms. -/
theorem space_map_comp (X : SimplicialObject TopCat.{u}) {n m p : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (g : m ⟶ p) :
    spaceHom X (f ≫ g).unop = Hom.comp (spaceHom X f.unop) (spaceHom X g.unop) := sorry

/-- The simplicial object of whole spaces `n ↦ X_n` in `Zariski X`. -/
def space (X : SimplicialObject TopCat.{u}) : SimplicialObject (Zariski X) where
  obj n := top X n.unop
  map f := spaceHom X f.unop
  map_id := space_map_id X
  map_comp := space_map_comp X

/-- The simplicial object `n ↦ Z_{X_n}` of free abelian representable presheaves on
`Zariski X`. -/
def freeAbelian (X : SimplicialObject TopCat.{u}) :
    SimplicialObject ((Zariski X)ᵒᵖ ⥤ AddCommGrpCat.{0}) :=
  space X ⋙ FreeAbelianYoneda.functor

/-- The value of `freeAbelian X` at `n` is the free abelian representable at the whole space
`X_n`. -/
theorem freeAbelian_obj (X : SimplicialObject TopCat.{u}) (n : SimplexCategory) :
    (freeAbelian X).obj (op n) = FreeAbelianYoneda.obj (top X n) := sorry

/-- The constant abelian presheaf `ℤ` on `Zariski X`. -/
abbrev constantInteger (X : SimplicialObject TopCat.{u}) :
    (Zariski X)ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (Functor.const (Zariski X)ᵒᵖ).obj (AddCommGrpCat.of ℤ)

/-- The component of the canonical augmentation `Z_{X_n} ⟶ ℤ` at a simplex `n`. -/
def augmented_hom_app (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    (freeAbelian X).obj n ⟶ constantInteger X :=
  (FreeAbelianYoneda.homEquiv ((space X).obj n) (constantInteger X)).symm
    ((1 : ℤ) : (constantInteger X).obj (op ((space X).obj n)))

/-- Naturality of the degreewise augmentation `Z_{X_n} ⟶ ℤ`. -/
theorem augmented_hom_naturality (X : SimplicialObject TopCat.{u}) :
    ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (f : n ⟶ m),
      (freeAbelian X).map f ≫ augmented_hom_app X m =
        augmented_hom_app X n ≫
          ((SimplicialObject.const _).obj (constantInteger X)).map f := sorry

/-- The natural transformation `freeAbelian X ⟶ const ℤ`. -/
def augmented_hom (X : SimplicialObject TopCat.{u}) :
    freeAbelian X ⟶ (SimplicialObject.const _).obj (constantInteger X) where
  app := augmented_hom_app X
  naturality := augmented_hom_naturality X

/-- The augmented simplicial object of free abelian representables `Z_{X_•}` over the constant
presheaf `ℤ`. -/
def augmented (X : SimplicialObject TopCat.{u}) :
    SimplicialObject.Augmented ((Zariski X)ᵒᵖ ⥤ AddCommGrpCat.{0}) where
  left := freeAbelian X
  right := constantInteger X
  hom := augmented_hom X

/-- The alternating-face chain complex `… → Z_{X_2} → Z_{X_1} → Z_{X_0}`. -/
abbrev complex (X : SimplicialObject TopCat.{u}) :
    ChainComplex ((Zariski X)ᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ :=
  (alternatingFaceMapComplex _).obj (SimplicialObject.Augmented.drop.obj (augmented X))

/-- The canonical chain-map augmentation from `complex X` to the constant presheaf `ℤ`
concentrated in degree zero. -/
def augmentation (X : SimplicialObject TopCat.{u}) :
    complex X ⟶ (ChainComplex.single₀ _).obj (constantInteger X) :=
  AlternatingFaceMapComplex.ε.app (augmented X)

end Zariski

end AlgebraicTopology.SimplicialSpace

