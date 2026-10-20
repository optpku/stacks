module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Map
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Presheaf
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
public import ReasLib.CategoryTheory.Sites.Localization.Presheaf
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Augmentation
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
  rfl

/-- Compatible augmentations give compatible tautological sections on every summand. -/
theorem toElementsFamilyHom_condition {K L : FormalCoproduct.{w} C} (φ : K ⟶ L)
    (α : FormalCoproduct.toPresheaf.obj K ⟶ G)
    (β : FormalCoproduct.toPresheaf.obj L ⟶ G)
    (h : FormalCoproduct.toPresheaf.map φ ≫ β = α) (i : K.I) :
    G.map (φ.φ i).op (tautologicalSection β (φ.f i)) = tautologicalSection α i := sorry

/-- A morphism compatible with augmentations induces a morphism of localized families. -/
def toElementsFamilyHom {K L : FormalCoproduct.{w} C} (φ : K ⟶ L)
    (α : FormalCoproduct.toPresheaf.obj K ⟶ G)
    (β : FormalCoproduct.toPresheaf.obj L ⟶ G)
    (h : FormalCoproduct.toPresheaf.map φ ≫ β = α) :
    toElementsFamily α ⟶ toElementsFamily β where
  f := φ.f
  φ i := (homMk _ _ (φ.φ i).op (toElementsFamilyHom_condition φ α β h i)).op

/-- `toElementsFamilyHom` retains the reindexing function of the original morphism. -/
theorem toElementsFamilyHom_f {K L : FormalCoproduct.{w} C} (φ : K ⟶ L)
    (α : FormalCoproduct.toPresheaf.obj K ⟶ G)
    (β : FormalCoproduct.toPresheaf.obj L ⟶ G)
    (h : FormalCoproduct.toPresheaf.map φ ≫ β = α) :
    (toElementsFamilyHom φ α β h).f = φ.f :=
  rfl

variable (K : HypercoveringOf J G)

/-- Lifting the augmentation components preserves simplicial identities and composition. -/
theorem toLocalizedSimplicial_laws :
    (∀ n, toElementsFamilyHom (K.simplicial.map (𝟙 n))
      (K.augmentation.app n) (K.augmentation.app n) (K.augmentation.naturality (𝟙 n)) =
        𝟙 (toElementsFamily (K.augmentation.app n))) ∧
    (∀ {n m l} (f : n ⟶ m) (g : m ⟶ l),
      toElementsFamilyHom (K.simplicial.map (f ≫ g))
        (K.augmentation.app n) (K.augmentation.app l) (K.augmentation.naturality (f ≫ g)) =
      toElementsFamilyHom (K.simplicial.map f)
        (K.augmentation.app n) (K.augmentation.app m) (K.augmentation.naturality f) ≫
      toElementsFamilyHom (K.simplicial.map g)
        (K.augmentation.app m) (K.augmentation.app l) (K.augmentation.naturality g)) := sorry

/-- The simplicial family on the localization obtained from an augmented hypercovering. -/
def toLocalizedSimplicial : SimplicialObject (SR(G.Elementsᵒᵖ)) where
  obj n := toElementsFamily (K.augmentation.app n)
  map f := toElementsFamilyHom (K.simplicial.map f)
    (K.augmentation.app _) (K.augmentation.app _) (K.augmentation.naturality f)
  map_id := (toLocalizedSimplicial_laws J K).1
  map_comp := (toLocalizedSimplicial_laws J K).2

/-- The localized simplicial family with terminal augmentation is a local hypercover. -/
theorem toLocalizedTerminal_isLocalHypercover :
    (hypercoveringAugmentedPresheaf (toLocalizedSimplicial J K)
      (terminalAugmentation (toLocalizedSimplicial J K))).IsLocalHypercover
        (Presheaf.localizationSite J G) := sorry

/-- The object map of `toLocalizedSimplicial` is `toElementsFamily` of the augmentation
component. -/
theorem toLocalizedSimplicial_obj (n : SimplexCategoryᵒᵖ) :
    (toLocalizedSimplicial J K).obj n = toElementsFamily (K.augmentation.app n) :=
  rfl

/-- The site-level hypercovering of `C / G` associated to a hypercovering of `G`. -/
def toLocalizedTerminal : HypercoveringOf.Terminal (Presheaf.localizationSite J G) where
  simplicial := toLocalizedSimplicial J K
  augmentation := terminalAugmentation (toLocalizedSimplicial J K)
  isLocalHypercover := toLocalizedTerminal_isLocalHypercover J K

/-- The underlying simplicial object of `toLocalizedTerminal` is `toLocalizedSimplicial`. -/
theorem toLocalizedTerminal_simplicial :
    (toLocalizedTerminal J K).simplicial = toLocalizedSimplicial J K :=
  rfl

variable {K}

/-- Project a formal coproduct of objects of `C / G` to a formal coproduct in `C`. -/
def ofElementsFamily (L : FormalCoproduct.{w} G.Elementsᵒᵖ) :
    FormalCoproduct.{w} C :=
  FormalCoproduct.mapObj (Presheaf.localizationForget G) L

/-- The augmentation reconstructed from the elements of a localized family is natural. -/
theorem ofElementsAugmentation_naturality (L : FormalCoproduct.{w} G.Elementsᵒᵖ)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (FormalCoproduct.toPresheaf.obj (ofElementsFamily L)).map f ≫
      TypeCat.ofHom (fun s ↦
      let σ := (ofElementsFamily L).toPresheafObjEquiv Y s
      G.map σ.2.op (L.obj σ.1).unop.2) =
    TypeCat.ofHom (fun s ↦
      let σ := (ofElementsFamily L).toPresheafObjEquiv X s
      G.map σ.2.op (L.obj σ.1).unop.2) ≫ G.map f := sorry

/-- The augmentation reconstructed from the tautological sections of a localized family. -/
def ofElementsAugmentation (L : FormalCoproduct.{w} G.Elementsᵒᵖ) :
    FormalCoproduct.toPresheaf.obj (ofElementsFamily L) ⟶ G where
  app X := TypeCat.ofHom (fun s ↦
      let σ := (ofElementsFamily L).toPresheafObjEquiv X s
      G.map σ.2.op (L.obj σ.1).unop.2)
  naturality _ _ f := ofElementsAugmentation_naturality L f

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

/-- The reconstructed augmentation is compatible with simplicial operators. -/
theorem ofLocalizedAugmentation_naturality {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (hypercoveringPresheaf (ofLocalizedSimplicial J L)).map f ≫
      ofElementsAugmentation (L.simplicial.obj m) =
    ofElementsAugmentation (L.simplicial.obj n) ≫
      ((SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj G).map f := sorry

/-- The augmentation of `ofLocalizedSimplicial` rebuilt from tautological `G`-sections. -/
def ofLocalizedAugmentation :
    hypercoveringPresheaf (ofLocalizedSimplicial J L) ⟶
      (SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj G where
  app n := ofElementsAugmentation (L.simplicial.obj n)
  naturality _ _ f := ofLocalizedAugmentation_naturality J L f

/-- Projecting a terminal local hypercover from the localization gives a local hypercover. -/
theorem ofLocalizedTerminal_isLocalHypercover :
    (hypercoveringAugmentedPresheaf (ofLocalizedSimplicial J L)
      (ofLocalizedAugmentation J L)).IsLocalHypercover J := sorry

/-- The hypercovering of `G` associated to a site-level hypercovering of `C / G`. -/
def ofLocalizedTerminal : HypercoveringOf J G where
  simplicial := ofLocalizedSimplicial J L
  augmentation := ofLocalizedAugmentation J L
  isLocalHypercover := ofLocalizedTerminal_isLocalHypercover J L

/-- The underlying simplicial object of `ofLocalizedTerminal` is `ofLocalizedSimplicial`. -/
theorem ofLocalizedTerminal_simplicial :
    (ofLocalizedTerminal J L).simplicial = ofLocalizedSimplicial J L :=
  rfl

variable (G)

/-- The two hypercovering conversions are mutually inverse. -/
theorem hypercoveringEquivLocalizedTerminal_inverse_laws :
    (∀ K : HypercoveringOf J G, ofLocalizedTerminal J (toLocalizedTerminal J K) = K) ∧
    (∀ L : HypercoveringOf.Terminal (Presheaf.localizationSite J G),
      toLocalizedTerminal J (ofLocalizedTerminal J L) = L) := sorry

/-- A hypercovering of `G` is the same thing as a hypercovering of the site `C / G`. -/
def hypercoveringEquivLocalizedTerminal :
    HypercoveringOf J G ≃ HypercoveringOf.Terminal (Presheaf.localizationSite J G) where
  toFun K := toLocalizedTerminal J K
  invFun L := ofLocalizedTerminal J L
  left_inv := (hypercoveringEquivLocalizedTerminal_inverse_laws J G).1
  right_inv := (hypercoveringEquivLocalizedTerminal_inverse_laws J G).2

/-- The forward map of `hypercoveringEquivLocalizedTerminal` is `toLocalizedTerminal`. -/
theorem hypercoveringEquivLocalizedTerminal_apply (K : HypercoveringOf J G) :
    hypercoveringEquivLocalizedTerminal J G K = toLocalizedTerminal J K :=
  rfl

/-- The inverse map of `hypercoveringEquivLocalizedTerminal` is `ofLocalizedTerminal`. -/
theorem hypercoveringEquivLocalizedTerminal_symm
    (L : HypercoveringOf.Terminal (Presheaf.localizationSite J G)) :
    (hypercoveringEquivLocalizedTerminal J G).symm L = ofLocalizedTerminal J L :=
  rfl


open CategoryTheory.SemiRepresentableFamily

variable {G} (K : HypercoveringOf J G)

/-- Lifting a slice arrow records the section obtained by restriction of its augmentation. -/
def liftSlice {A : FormalCoproduct.{w} C}
    (α : FormalCoproduct.toPresheaf.obj A ⟶ G) (i : A.I) :
    CategoryTheory.Over (A.obj i) ⥤ CategoryTheory.Over (toElementsObj α i) where
  obj U := CategoryTheory.Over.mk
    (homMk _ ⟨op U.left, G.map U.hom.op (tautologicalSection α i)⟩ U.hom.op rfl).op
  map {U V} f := CategoryTheory.Over.homMk
    (homMk _ _ f.left.op (by
      change G.map f.left.op (G.map V.hom.op (tautologicalSection α i)) =
        G.map U.hom.op (tautologicalSection α i)
      rw [← Functor.map_comp_apply, ← op_comp, CategoryTheory.Over.w])).op
    (by
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      exact congrArg Quiver.Hom.op (CategoryTheory.Over.w f))
  map_id U := by ext; rfl
  map_comp f g := by ext; rfl

/-- The degreewise lift from slices in the original family to slices in the localization. -/
def liftStage (n : SimplexCategoryᵒᵖ) :
    OverSite (K.simplicial.obj n) ⥤ OverSite ((toLocalizedSimplicial J K).obj n) :=
  CategoryTheory.Sigma.desc fun i ↦
    liftSlice (K.augmentation.app n) i ⋙ overIncl ((toLocalizedSimplicial J K).obj n) i

/-- The degreewise projection of localized slices to slices in the original family. -/
def projectStage (n : SimplexCategoryᵒᵖ) :
    OverSite ((toLocalizedSimplicial J K).obj n) ⥤ OverSite (K.simplicial.obj n) :=
  CategoryTheory.Sigma.desc fun i ↦
    CategoryTheory.Over.post (Presheaf.localizationForget G) ⋙ overIncl (K.simplicial.obj n) i

/-- Lifting slices by their tautological sections commutes with simplicial relocalization. -/
theorem toLocalizedTotalSite_laws {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (overSiteDiagram K.simplicial).map f ≫ (liftStage J K m).toCatHom =
      (liftStage J K n).toCatHom ≫ (overSiteDiagram (toLocalizedSimplicial J K)).map f := sorry

/-- The functor from the original total site to the localized total site, retaining degrees,
summand indices, and underlying arrows, and recording the tautological sections. -/
def toLocalizedTotalSite :
    Grothendieck (overSiteDiagram K.simplicial) ⥤
      Grothendieck (overSiteDiagram (toLocalizedSimplicial J K)) := by
  exact Grothendieck.map
    { app n := (liftStage J K n).toCatHom
      naturality _ _ f := toLocalizedTotalSite_laws J K f }

/-- Projecting localized slices commutes with simplicial relocalization. -/
theorem fromLocalizedTotalSite_laws {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (overSiteDiagram (toLocalizedSimplicial J K)).map f ≫ (projectStage J K m).toCatHom =
      (projectStage J K n).toCatHom ≫ (overSiteDiagram K.simplicial).map f := sorry

/-- The functor from the localized total site to the original total site obtained by forgetting
the tautological sections. -/
def fromLocalizedTotalSite :
    Grothendieck (overSiteDiagram (toLocalizedSimplicial J K)) ⥤
      Grothendieck (overSiteDiagram K.simplicial) := by
  exact Grothendieck.map
    { app n := (projectStage J K n).toCatHom
      naturality _ _ f := fromLocalizedTotalSite_laws J K f }

/-- Lifting and forgetting sections are inverse on the total localization categories. -/
theorem localizedTotalSiteEquivalence_laws :
    (toLocalizedTotalSite J K ⋙ fromLocalizedTotalSite J K = 𝟭 _) ∧
    (fromLocalizedTotalSite J K ⋙ toLocalizedTotalSite J K = 𝟭 _) := sorry

/-- The original total localization category is equivalent to that of the localized family. -/
def localizedTotalSiteEquivalence :
    Grothendieck (overSiteDiagram K.simplicial) ≌
      Grothendieck (overSiteDiagram (toLocalizedSimplicial J K)) :=
  Equivalence.mk (toLocalizedTotalSite J K) (fromLocalizedTotalSite J K)
    (eqToIso (localizedTotalSiteEquivalence_laws J K).1.symm)
    (eqToIso (localizedTotalSiteEquivalence_laws J K).2)

/-- A sieve covers the original total site exactly when its image covers the localized
family's total site. -/
theorem localizedTotalSiteEquivalence_cover_iff
    {X : Grothendieck (overSiteDiagram K.simplicial)} (S : Sieve X) :
    S ∈ overSiteTotalTopology J K.simplicial X ↔
      S.functorPushforward (toLocalizedTotalSite J K) ∈
        overSiteTotalTopology (Presheaf.localizationSite J G) (toLocalizedSimplicial J K)
          ((toLocalizedTotalSite J K).obj X) := sorry

end CategoryTheory.HypercoveringOf
