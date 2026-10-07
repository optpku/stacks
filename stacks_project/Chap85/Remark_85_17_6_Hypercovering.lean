module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Map
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Presheaf
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
public import stacks_project.Chap85.Remark_85_17_6_Localization
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Hypercoverings of a presheaf as terminal hypercoverings of `C / G`

A hypercovering of a set-valued presheaf `G` is converted to a site-level hypercovering of the
terminal presheaf on `C / G` by recording the tautological `G`-sections as objects of
`G.Elementsᵒᵖ`. The reverse conversion projects along `localizationForget`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryOfElements
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.HypercoveringOf

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasEqualizers C] [HasPullbacks C]
variable {G : Cᵒᵖ ⥤ Type (max w v)}

/-- The tautological `G`-section on a formal-coproduct summand, read from an augmentation. -/
def tautologicalSection {K : FormalCoproduct.{w} C}
    (α : FormalCoproduct.toPresheaf.obj K ⟶ G) (i : K.I) :
    G.obj (op (K.obj i)) :=
  (α.app (op (K.obj i))) (K.toPresheafObjMk (op (K.obj i)) i (𝟙 _))

/-- The object of `C / G` associated to a formal-coproduct summand and its tautological
`G`-section. -/
def toElementsObj {K : FormalCoproduct.{w} C}
    (α : FormalCoproduct.toPresheaf.obj K ⟶ G) (i : K.I) :
    G.Elementsᵒᵖ :=
  op ⟨op (K.obj i), tautologicalSection α i⟩

/-- Convert a formal coproduct over `C` with an augmentation to `G` into a formal coproduct
of objects of `C / G`. -/
def toElementsFamily {K : FormalCoproduct.{w} C}
    (α : FormalCoproduct.toPresheaf.obj K ⟶ G) :
    FormalCoproduct.{w} G.Elementsᵒᵖ where
  I := K.I
  obj i := toElementsObj α i

/-- The object map of `toElementsFamily` records tautological `G`-sections. -/
theorem toElementsFamily_obj {K : FormalCoproduct.{w} C}
    (α : FormalCoproduct.toPresheaf.obj K ⟶ G) (i : K.I) :
    (toElementsFamily α).obj i = toElementsObj α i :=
  sorry

/-- A morphism of augmented formal coproducts over `G` induces a morphism of the associated
families in `C / G`. -/
def toElementsFamilyHom {K L : FormalCoproduct.{w} C} (φ : K ⟶ L)
    (α : FormalCoproduct.toPresheaf.obj K ⟶ G)
    (β : FormalCoproduct.toPresheaf.obj L ⟶ G) :
    toElementsFamily α ⟶ toElementsFamily β where
  f := φ.f
  φ i :=
    (homMk
        ⟨op (L.obj (φ.f i)), tautologicalSection β (φ.f i)⟩
        ⟨op (K.obj i), tautologicalSection α i⟩
        (φ.φ i).op sorry).op

/-- `toElementsFamilyHom` retains the reindexing function of the original morphism. -/
theorem toElementsFamilyHom_f {K L : FormalCoproduct.{w} C} (φ : K ⟶ L)
    (α : FormalCoproduct.toPresheaf.obj K ⟶ G)
    (β : FormalCoproduct.toPresheaf.obj L ⟶ G) :
    (toElementsFamilyHom φ α β).f = φ.f :=
  sorry

variable (K : HypercoveringOf J G)

/-- The simplicial semi-representable family on `C / G` associated to a hypercovering of `G`. -/
def toLocalizedSimplicial : SimplicialObject (SR(G.Elementsᵒᵖ)) where
  obj n := toElementsFamily (K.augmentation.app n)
  map {n m} f :=
    toElementsFamilyHom (K.simplicial.map f) (K.augmentation.app n) (K.augmentation.app m)
  map_id := sorry
  map_comp := sorry

/-- The object map of `toLocalizedSimplicial` is `toElementsFamily` of the augmentation
component. -/
theorem toLocalizedSimplicial_obj (n : SimplexCategoryᵒᵖ) :
    (toLocalizedSimplicial J K).obj n = toElementsFamily (K.augmentation.app n) :=
  sorry

/-- The site-level hypercovering of `C / G` associated to a hypercovering of `G`. -/
def toLocalizedTerminal : HypercoveringOf.Terminal (Presheaf.localizationSite J G) where
  simplicial := toLocalizedSimplicial J K
  augmentation := terminalAugmentation (toLocalizedSimplicial J K)
  isLocalHypercover := sorry

/-- The underlying simplicial object of `toLocalizedTerminal` is `toLocalizedSimplicial`. -/
theorem toLocalizedTerminal_simplicial :
    (toLocalizedTerminal J K).simplicial = toLocalizedSimplicial J K :=
  sorry

variable {K}

/-- Project a formal coproduct of objects of `C / G` to a formal coproduct in `C`. -/
def ofElementsFamily (L : FormalCoproduct.{w} G.Elementsᵒᵖ) :
    FormalCoproduct.{w} C :=
  FormalCoproduct.mapObj (Presheaf.localizationForget G) L

/-- The underlying object of an element of `C / G` is the image of the elements projection. -/
theorem unop_fst_eq_op_localizationForget (e : G.Elementsᵒᵖ) :
    e.unop.1 = op ((Presheaf.localizationForget G).obj e) :=
  sorry

/-- Rebuild the augmentation to `G` from the tautological sections of a family in `C / G`. -/
def ofElementsAugmentation (L : FormalCoproduct.{w} G.Elementsᵒᵖ) :
    FormalCoproduct.toPresheaf.obj (ofElementsFamily L) ⟶ G where
  app X := TypeCat.ofHom (fun s =>
    let σ := (ofElementsFamily L).toPresheafObjEquiv X s
    (G.map σ.2.op ≫ eqToHom (congrArg G.obj (Opposite.op_unop X)))
      (eqToHom (congrArg G.obj (unop_fst_eq_op_localizationForget (L.obj σ.1)).symm)
        (L.obj σ.1).unop.2))
  naturality := sorry

/-- Evaluating `ofElementsAugmentation` on a canonical coproduct summand recovers the
transported tautological section. -/
theorem ofElementsAugmentation_app_objMk (L : FormalCoproduct.{w} G.Elementsᵒᵖ)
    (X : Cᵒᵖ) (i : L.I) (g : X.unop ⟶ (ofElementsFamily L).obj i) :
    (ofElementsAugmentation L).app X
        ((ofElementsFamily L).toPresheafObjMk X i g) =
      G.map g.op (L.obj i).unop.2 :=
  sorry

variable (L : HypercoveringOf.Terminal (Presheaf.localizationSite J G))

/-- The simplicial semi-representable family on `C` obtained by projecting a site-level
hypercovering of `C / G`. -/
def ofLocalizedSimplicial : SimplicialObject (SR(C)) :=
  L.simplicial ⋙ FormalCoproduct.map (Presheaf.localizationForget G)

/-- The underlying simplicial object of `ofLocalizedSimplicial` is componentwise
`localizationForget`. -/
theorem ofLocalizedSimplicial_eq :
    ofLocalizedSimplicial J L =
      L.simplicial ⋙ FormalCoproduct.map (Presheaf.localizationForget G) :=
  sorry

/-- The augmentation of `ofLocalizedSimplicial` rebuilt from tautological `G`-sections. -/
def ofLocalizedAugmentation :
    hypercoveringPresheaf (ofLocalizedSimplicial J L) ⟶
      (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj G where
  app n := ofElementsAugmentation (L.simplicial.obj n)
  naturality := sorry

/-- The hypercovering of `G` associated to a site-level hypercovering of `C / G`. -/
def ofLocalizedTerminal : HypercoveringOf J G where
  simplicial := ofLocalizedSimplicial J L
  augmentation := ofLocalizedAugmentation J L
  isLocalHypercover := sorry

/-- The underlying simplicial object of `ofLocalizedTerminal` is `ofLocalizedSimplicial`. -/
theorem ofLocalizedTerminal_simplicial :
    (ofLocalizedTerminal J L).simplicial = ofLocalizedSimplicial J L :=
  sorry

variable (G)

/-- A hypercovering of `G` is the same thing as a hypercovering of the site `C / G`. -/
def hypercoveringEquivLocalizedTerminal :
    HypercoveringOf J G ≃ HypercoveringOf.Terminal (Presheaf.localizationSite J G) where
  toFun K := toLocalizedTerminal J K
  invFun L := ofLocalizedTerminal J L
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `hypercoveringEquivLocalizedTerminal` is `toLocalizedTerminal`. -/
theorem hypercoveringEquivLocalizedTerminal_apply (K : HypercoveringOf J G) :
    hypercoveringEquivLocalizedTerminal J G K = toLocalizedTerminal J K :=
  sorry

/-- The inverse map of `hypercoveringEquivLocalizedTerminal` is `ofLocalizedTerminal`. -/
theorem hypercoveringEquivLocalizedTerminal_symm
    (L : HypercoveringOf.Terminal (Presheaf.localizationSite J G)) :
    (hypercoveringEquivLocalizedTerminal J G).symm L = ofLocalizedTerminal J L :=
  sorry

end CategoryTheory.HypercoveringOf
