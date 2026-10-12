/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import ReasLib.CategoryTheory.Functor.FreeAbelianYoneda
public import ReasLib.Topology.Category.TopCat.DiagramOpens

/-!
# Free abelian resolution of a simplicial diagram of spaces

The whole stages of a simplicial topological space represent free abelian presheaves on
its category of diagram opens. Their alternating-face complex is augmented over ℤ.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicTopology HomologicalComplex
open scoped Simplicial

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject.ZariskiResolution

/-- The whole stage `X_n`, viewed as a diagram open of `X`. -/
def stageTop (X : SimplicialObject TopCat.{u}) (n : SimplexCategory) :
    TopCat.DiagramOpens X := TopCat.DiagramOpens.ofOpens X (op n) ⊤

/-- A simplex operator into the base of a diagram open carries that open into the whole stage. -/
theorem stageHomMk_mapsTo {X : SimplicialObject TopCat.{u}}
    {U : TopCat.DiagramOpens X} {n : SimplexCategory}
    (φ : n ⟶ U.base.unop) :
    Set.MapsTo (X.map φ.op).hom U.opens (⊤ : Opens (X.obj (op n))) := sorry

/-- The diagram-open morphism from `U` into a whole stage induced by a simplex operator. -/
def stageHomMk {X : SimplicialObject TopCat.{u}}
    {U : TopCat.DiagramOpens X} {n : SimplexCategory}
    (φ : n ⟶ U.base.unop) : U ⟶ stageTop X n :=
  TopCat.DiagramOpens.homMk φ.op (stageHomMk_mapsTo φ)

/-- Recover a morphism into a whole stage from its underlying simplex operator. -/
theorem stageHomEquiv_left_inv {X : SimplicialObject TopCat.{u}}
    (U : TopCat.DiagramOpens X) (n : SimplexCategory) (f : U ⟶ stageTop X n) :
    stageHomMk f.base.unop = f := sorry

/-- Recover a simplex operator from its morphism into a whole stage. -/
theorem stageHomEquiv_right_inv {X : SimplicialObject TopCat.{u}}
    (U : TopCat.DiagramOpens X) (n : SimplexCategory) (φ : n ⟶ U.base.unop) :
    (stageHomMk φ).base.unop = φ := sorry

/-- Morphisms from a diagram open into the whole stage `X_n` are simplex operators. -/
def stageHomEquiv {X : SimplicialObject TopCat.{u}}
    (U : TopCat.DiagramOpens X) (n : SimplexCategory) :
    (U ⟶ stageTop X n) ≃ (n ⟶ U.base.unop) where
  toFun f := f.base.unop
  invFun := stageHomMk
  left_inv := stageHomEquiv_left_inv U n
  right_inv := stageHomEquiv_right_inv U n

/-- A simplex operator carries a whole stage into a whole stage. -/
theorem stageHom_mapsTo (X : SimplicialObject TopCat.{u})
    {n m : SimplexCategory} (φ : m ⟶ n) :
    Set.MapsTo (X.map φ.op).hom (⊤ : Opens (X.obj (op n)))
      (⊤ : Opens (X.obj (op m))) := sorry

/-- The diagram-open morphism between whole stages induced by a simplex operator. -/
def stageHom (X : SimplicialObject TopCat.{u})
    {n m : SimplexCategory} (φ : m ⟶ n) : stageTop X n ⟶ stageTop X m :=
  TopCat.DiagramOpens.homMk φ.op (stageHom_mapsTo X φ)

/-- The identity simplex operator induces the identity morphism between whole stages. -/
theorem space_map_id (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    stageHom X (𝟙 n).unop = 𝟙 (stageTop X n.unop) := sorry

/-- Composition of simplex operators induces composition of whole-stage morphisms. -/
theorem space_map_comp (X : SimplicialObject TopCat.{u})
    {n m p : SimplexCategoryᵒᵖ} (f : n ⟶ m) (g : m ⟶ p) :
    stageHom X (f ≫ g).unop = stageHom X f.unop ≫ stageHom X g.unop := sorry

/-- The simplicial object of whole stages of `X` in its diagram-open category. -/
def space (X : SimplicialObject TopCat.{u}) :
    SimplicialObject (TopCat.DiagramOpens X) where
  obj n := stageTop X n.unop
  map f := stageHom X f.unop
  map_id := space_map_id X
  map_comp := space_map_comp X

/-- The simplicial free abelian presheaves represented by the whole stages of `X`. -/
def freeAbelian (X : SimplicialObject TopCat.{u}) :
    SimplicialObject ((TopCat.DiagramOpens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) :=
  space X ⋙ FreeAbelianYoneda.functor

/-- The presheaf at a simplex is the free abelian presheaf represented by that whole stage. -/
theorem freeAbelian_obj (X : SimplicialObject TopCat.{u}) (n : SimplexCategory) :
    (freeAbelian X).obj (op n) = FreeAbelianYoneda.obj (stageTop X n) := sorry

/-- The constant integer-valued presheaf on the category of diagram opens of `X`. -/
abbrev constantInteger (X : SimplicialObject TopCat.{u}) :
    (TopCat.DiagramOpens X)ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (Functor.const (TopCat.DiagramOpens X)ᵒᵖ).obj (AddCommGrpCat.of ℤ)

/-- At each stage, the augmentation sends each free generator to `1 : ℤ`. -/
def augmented_hom_app (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    (freeAbelian X).obj n ⟶ constantInteger X :=
  (FreeAbelianYoneda.homEquiv ((space X).obj n) (constantInteger X)).symm
    ((1 : ℤ) : (constantInteger X).obj (op ((space X).obj n)))

/-- The degreewise augmentation commutes with all simplex operators. -/
theorem augmented_hom_naturality (X : SimplicialObject TopCat.{u}) :
    ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (f : n ⟶ m),
      (freeAbelian X).map f ≫ augmented_hom_app X m =
        augmented_hom_app X n ≫
          ((SimplicialObject.const _).obj (constantInteger X)).map f := sorry

/-- The natural augmentation of the simplicial free abelian presheaf to constant ℤ. -/
def augmented_hom (X : SimplicialObject TopCat.{u}) :
    freeAbelian X ⟶ (SimplicialObject.const _).obj (constantInteger X) where
  app := augmented_hom_app X
  naturality := augmented_hom_naturality X

/-- The augmented simplicial object of free abelian presheaves on diagram opens. -/
def augmented (X : SimplicialObject TopCat.{u}) :
    SimplicialObject.Augmented ((TopCat.DiagramOpens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) where
  left := freeAbelian X
  right := constantInteger X
  hom := augmented_hom X

/-- The alternating-face chain complex of free abelian whole-stage presheaves. -/
abbrev complex (X : SimplicialObject TopCat.{u}) :
    ChainComplex ((TopCat.DiagramOpens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ :=
  (alternatingFaceMapComplex _).obj (SimplicialObject.Augmented.drop.obj (augmented X))

/-- The canonical augmentation to the constant integer presheaf in degree zero. -/
def augmentation (X : SimplicialObject TopCat.{u}) :
    complex X ⟶ (ChainComplex.single₀ _).obj (constantInteger X) :=
  AlternatingFaceMapComplex.ε.app (augmented X)

/-- The whole-stage free abelian resolution has a quasi-isomorphic augmentation to constant ℤ. -/
instance augmentation_quasiIso (X : SimplicialObject TopCat.{u}) :
    QuasiIso (augmentation X) := sorry

end CategoryTheory.SimplicialObject.ZariskiResolution
