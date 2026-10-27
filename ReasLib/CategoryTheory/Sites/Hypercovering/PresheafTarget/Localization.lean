/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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

omit [HasEqualizers C] [HasPullbacks C] in
private theorem presheaf_objMk_map (A : FormalCoproduct.{w} C)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (i : A.I) (g : X.unop ⟶ A.obj i) :
    (FormalCoproduct.toPresheaf.obj A).map f (A.toPresheafObjMk X i g) =
      A.toPresheafObjMk Y i (f.unop ≫ g) := by
  exact (congrArg (fun k ↦ k (ULift.up g))
    ((Sigma.ι (fun j : A.I ↦ uliftYoneda.{w}.obj (A.obj j)) i).naturality f)).symm

omit [HasEqualizers C] [HasPullbacks C] in
private theorem augmentation_objMk_naturality {A : FormalCoproduct.{w} C}
    (α : FormalCoproduct.toPresheaf.obj A ⟶ G) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (i : A.I) (g : X.unop ⟶ A.obj i) :
    G.map f (α.app X (A.toPresheafObjMk X i g)) =
      α.app Y (A.toPresheafObjMk Y i (f.unop ≫ g)) := by
  rw [← α.naturality_apply, presheaf_objMk_map]

omit [HasEqualizers C] [HasPullbacks C] in
private theorem presheaf_map_objMk {A B : FormalCoproduct.{w} C} (φ : A ⟶ B)
    (X : Cᵒᵖ) (i : A.I) (g : X.unop ⟶ A.obj i) :
    (FormalCoproduct.toPresheaf.map φ).app X (A.toPresheafObjMk X i g) =
      B.toPresheafObjMk X (φ.f i) (g ≫ φ.φ i) := by
  exact congrArg (fun η ↦ η.app X (ULift.up g))
    (Sigma.ι_desc (fun j ↦ uliftYoneda.{w}.map (φ.φ j) ≫
      Sigma.ι (fun k : B.I ↦ uliftYoneda.{w}.obj (B.obj k)) (φ.f j)) i)

omit [HasEqualizers C] [HasPullbacks C] in
private theorem presheafObjEquiv_objMk (A : FormalCoproduct.{w} C) (X : Cᵒᵖ)
    (i : A.I) (g : X.unop ⟶ A.obj i) :
    A.toPresheafObjEquiv X (A.toPresheafObjMk X i g) = ⟨i, g⟩ := by
  have h :
      (Sigma.ι (fun j : A.I ↦ uliftYoneda.{w}.obj (A.obj j)) i).app X ≫
        ((sigmaObjIso (fun j : A.I ↦ uliftYoneda.{w}.obj (A.obj j)) X).hom ≫
          (Types.coproductIso (fun j : A.I ↦ ULift.{w} (X.unop ⟶ A.obj j))).hom) =
      TypeCat.ofHom (fun x ↦ ⟨i, x⟩) := by
    rw [ι_comp_sigmaObjIso_hom_assoc, Types.coproductIso_ι_comp_hom]
  exact congrArg (fun f ↦ (Equiv.sigmaCongrRight fun _ ↦ Equiv.ulift)
    (f (ULift.up g))) h

omit [HasEqualizers C] [HasPullbacks C] in
private theorem presheaf_objMk_surjective (A : FormalCoproduct.{w} C) (X : Cᵒᵖ)
    (s : (FormalCoproduct.toPresheaf.obj A).obj X) :
    ∃ (i : A.I) (g : X.unop ⟶ A.obj i), A.toPresheafObjMk X i g = s := by
  obtain ⟨⟨i, g⟩, rfl⟩ := (A.toPresheafObjEquiv X).symm.surjective s
  refine ⟨i, g, (A.toPresheafObjEquiv X).injective ?_⟩
  rw [presheafObjEquiv_objMk, Equiv.apply_symm_apply]

/-- Compatible augmentations give compatible tautological sections on every summand. -/
theorem toElementsFamilyHom_condition {K L : FormalCoproduct.{w} C} (φ : K ⟶ L)
    (α : FormalCoproduct.toPresheaf.obj K ⟶ G)
    (β : FormalCoproduct.toPresheaf.obj L ⟶ G)
    (h : FormalCoproduct.toPresheaf.map φ ≫ β = α) (i : K.I) :
    G.map (φ.φ i).op (tautologicalSection β (φ.f i)) = tautologicalSection α i := by
  simpa only [tautologicalSection, augmentation_objMk_naturality, Category.comp_id,
    NatTrans.comp_app, types_comp_apply, presheaf_map_objMk, Category.id_comp, Quiver.Hom.unop_op] using
    congrArg (fun η ↦ η.app (op (K.obj i))
      (K.toPresheafObjMk (op (K.obj i)) i (𝟙 _))) h

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
        (K.augmentation.app m) (K.augmentation.app l) (K.augmentation.naturality g)) := by
  constructor
  · intro n
    simp only [K.simplicial.map_id]
    apply FormalCoproduct.hom_ext rfl
    intro i
    simp only [eqToHom_refl, Category.comp_id]
  · intro n m l f g
    simp only [K.simplicial.map_comp]
    apply FormalCoproduct.hom_ext rfl
    intro i
    simp only [eqToHom_refl, Category.comp_id]

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
      G.map σ.2.op (L.obj σ.1).unop.2) ≫ G.map f := by
  ext s
  obtain ⟨⟨i, g⟩, rfl⟩ := ((ofElementsFamily L).toPresheafObjEquiv X).symm.surjective s
  have hs : ((ofElementsFamily L).toPresheafObjEquiv X).symm ⟨i, g⟩ =
      (ofElementsFamily L).toPresheafObjMk X i g :=
    ((ofElementsFamily L).toPresheafObjEquiv X).injective (by
      rw [Equiv.apply_symm_apply, presheafObjEquiv_objMk])
  rw [hs]
  change G.map (((ofElementsFamily L).toPresheafObjEquiv Y
      ((FormalCoproduct.toPresheaf.obj (ofElementsFamily L)).map f
        ((ofElementsFamily L).toPresheafObjMk X i g))).2).op
      (L.obj (((ofElementsFamily L).toPresheafObjEquiv Y
        ((FormalCoproduct.toPresheaf.obj (ofElementsFamily L)).map f
          ((ofElementsFamily L).toPresheafObjMk X i g))).1)).unop.2 =
    G.map f (G.map (((ofElementsFamily L).toPresheafObjEquiv X
      ((ofElementsFamily L).toPresheafObjMk X i g)).2).op
        (L.obj (((ofElementsFamily L).toPresheafObjEquiv X
          ((ofElementsFamily L).toPresheafObjMk X i g)).1)).unop.2)
  rw [presheaf_objMk_map, presheafObjEquiv_objMk, presheafObjEquiv_objMk, op_comp]
  exact G.map_comp_apply g.op f (L.obj i).unop.2

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
  by
    change G.map (((ofElementsFamily L).toPresheafObjEquiv X
      ((ofElementsFamily L).toPresheafObjMk X i g)).2).op
      (L.obj (((ofElementsFamily L).toPresheafObjEquiv X
        ((ofElementsFamily L).toPresheafObjMk X i g)).1)).unop.2 = _
    rw [presheafObjEquiv_objMk]

private theorem of_toElementsAugmentation {A : FormalCoproduct.{w} C}
    (α : FormalCoproduct.toPresheaf.obj A ⟶ G) :
    ofElementsAugmentation (toElementsFamily α) = α := by
  ext X s
  obtain ⟨i, g, rfl⟩ := presheaf_objMk_surjective A X s
  calc
    (ofElementsAugmentation (toElementsFamily α)).app X (A.toPresheafObjMk X i g) =
        G.map g.op (tautologicalSection α i) :=
      ofElementsAugmentation_app_objMk (toElementsFamily α) X i g
    _ = α.app X (A.toPresheafObjMk X i g) := by
      simpa only [tautologicalSection, Category.comp_id, Quiver.Hom.unop_op] using
        augmentation_objMk_naturality α g.op i (𝟙 _)

private theorem to_ofElementsFamily (A : FormalCoproduct.{w} G.Elementsᵒᵖ) :
    toElementsFamily (ofElementsAugmentation A) = A := by
  cases A with
  | mk I A =>
    change FormalCoproduct.mk I (fun i ↦ toElementsObj (ofElementsAugmentation ⟨I, A⟩) i) =
      FormalCoproduct.mk I A
    apply congrArg (FormalCoproduct.mk I)
    funext i
    apply Opposite.unop_injective
    change (⟨op ((ofElementsFamily ⟨I, A⟩).obj i),
      tautologicalSection (ofElementsAugmentation ⟨I, A⟩) i⟩ : G.Elements) = (A i).unop
    refine CategoryTheory.Functor.Elements.ext _ _ ?_ ?_
    · rfl
    · change G.map (𝟙 _) (tautologicalSection (ofElementsAugmentation ⟨I, A⟩) i) = (A i).unop.2
      simp only [tautologicalSection, ofElementsAugmentation_app_objMk, op_id,
        CategoryTheory.Functor.map_id_apply]


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
      ((SimplicialObject.const (Cᵒᵖ ⥤ Type (max w v))).obj G).map f := by
  ext X s
  obtain ⟨⟨i, g⟩, rfl⟩ :=
    ((ofElementsFamily (L.simplicial.obj n)).toPresheafObjEquiv X).symm.surjective s
  have hs := (((ofElementsFamily (L.simplicial.obj n)).toPresheafObjEquiv X).injective
    (by rw [Equiv.apply_symm_apply, presheafObjEquiv_objMk]) :
      ((ofElementsFamily (L.simplicial.obj n)).toPresheafObjEquiv X).symm ⟨i, g⟩ =
        (ofElementsFamily (L.simplicial.obj n)).toPresheafObjMk X i g)
  rw [hs]
  change (ofElementsAugmentation (L.simplicial.obj m)).app X
      ((FormalCoproduct.toPresheaf.map
        (FormalCoproduct.mapHom (Presheaf.localizationForget G) (L.simplicial.map f))).app X
          ((ofElementsFamily (L.simplicial.obj n)).toPresheafObjMk X i g)) =
    (ofElementsAugmentation (L.simplicial.obj n)).app X
      ((ofElementsFamily (L.simplicial.obj n)).toPresheafObjMk X i g)
  erw [presheaf_map_objMk, ofElementsAugmentation_app_objMk,
    ofElementsAugmentation_app_objMk]
  change G.map (g ≫ ((L.simplicial.map f).φ i).unop.1.unop).op
      ((L.simplicial.obj m).obj ((L.simplicial.map f).f i)).unop.2 = _
  rw [op_comp, G.map_comp_apply]
  exact congrArg (G.map g.op) ((L.simplicial.map f).φ i).unop.2

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

omit [HasEqualizers C] [HasPullbacks C] in
private theorem elementsFamilyMap_faithful : (FormalCoproduct.map (Presheaf.localizationForget G)).Faithful where
  map_injective {A B} {φ ψ} h := by
    have h₁ := congrArg FormalCoproduct.Hom.f h
    change φ.f = ψ.f at h₁
    apply FormalCoproduct.hom_ext h₁
    intro i
    apply (Presheaf.localizationForget G).map_injective
    have h₂ : (Presheaf.localizationForget G).map (φ.φ i) ≫
        eqToHom (congrArg (fun k ↦ (Presheaf.localizationForget G).obj (B.obj (k i))) h₁) =
      (Presheaf.localizationForget G).map (ψ.φ i) :=
      ((FormalCoproduct.hom_ext_iff _ _).mp h).2 i
    simpa only [CategoryTheory.Functor.map_comp, eqToHom_map] using h₂

private theorem to_ofLocalizedSimplicial (L : HypercoveringOf.Terminal (Presheaf.localizationSite J G)) :
    toLocalizedSimplicial J (ofLocalizedTerminal J L) = L.simplicial := by
  letI := elementsFamilyMap_faithful (G := G)
  fapply CategoryTheory.Functor.ext
  · intro n
    exact to_ofElementsFamily (L.simplicial.obj n)
  · intro n m f
    apply (FormalCoproduct.map (Presheaf.localizationForget G)).map_injective
    simp only [CategoryTheory.Functor.map_comp, eqToHom_map]
    change (FormalCoproduct.map (Presheaf.localizationForget G)).map (L.simplicial.map f) =
      (𝟙 _) ≫ (FormalCoproduct.map (Presheaf.localizationForget G)).map
        (L.simplicial.map f) ≫ (𝟙 _)
    simp only [Category.id_comp, Category.comp_id]

variable (G)

/-- The two hypercovering conversions are mutually inverse. -/
theorem hypercoveringEquivLocalizedTerminal_inverse_laws :
    (∀ K : HypercoveringOf J G, ofLocalizedTerminal J (toLocalizedTerminal J K) = K) ∧
    (∀ L : HypercoveringOf.Terminal (Presheaf.localizationSite J G),
      toLocalizedTerminal J (ofLocalizedTerminal J L) = L) := by
  constructor
  · rintro ⟨S, α, h⟩
    have ha : ofLocalizedAugmentation J (toLocalizedTerminal J ⟨S, α, h⟩) = α := by
      apply NatTrans.ext
      funext n
      exact of_toElementsAugmentation (α.app n)
    change HypercoveringOf.mk S _ _ = HypercoveringOf.mk S α h
    congr 1
  · intro L
    have hs := to_ofLocalizedSimplicial J L
    change (toLocalizedTerminal J (ofLocalizedTerminal J L)).simplicial = L.simplicial at hs
    generalize ht : toLocalizedTerminal J (ofLocalizedTerminal J L) = T at hs ⊢
    cases L with
    | mk S α hL =>
      cases T with
      | mk S' β hT =>
        change S' = S at hs
        cases hs
        have ha : β = α := by
          apply NatTrans.ext
          funext n
          exact (Presheaf.terminalIsTerminal G.Elementsᵒᵖ).hom_ext _ _
        cases ha
        rfl

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

omit [HasEqualizers C] [HasPullbacks C] in
private theorem liftSlice_project_obj {A : FormalCoproduct.{w} C}
    (α : FormalCoproduct.toPresheaf.obj A ⟶ G) (i : A.I)
    (U : CategoryTheory.Over (toElementsObj α i)) :
    (liftSlice α i).obj ((CategoryTheory.Over.post (Presheaf.localizationForget G)).obj U) = U := by
  rcases U with ⟨U, ⟨⟨⟩⟩, f⟩
  induction U using Opposite.rec with
  | op U =>
    rcases U with ⟨X, x⟩
    rcases f with ⟨f, hf⟩
    change op (A.obj i) ⟶ X at f
    change G.map f (tautologicalSection α i) = x at hf
    subst x
    rfl

omit [HasEqualizers C] [HasPullbacks C] in
private theorem project_liftSlice {A : FormalCoproduct.{w} C}
    (α : FormalCoproduct.toPresheaf.obj A ⟶ G) (i : A.I) :
    CategoryTheory.Over.post (X := toElementsObj α i) (Presheaf.localizationForget G) ⋙
      liftSlice α i = 𝟭 _ := by
  fapply CategoryTheory.Functor.hext
  · intro U
    exact liftSlice_project_obj α i U
  · intro U V f
    rcases U with ⟨U, ⟨⟨⟩⟩, u⟩
    rcases V with ⟨V, ⟨⟨⟩⟩, v⟩
    induction U using Opposite.rec with
    | op U =>
      induction V using Opposite.rec with
      | op V =>
        rcases U with ⟨X, x⟩
        rcases V with ⟨Y, y⟩
        rcases u with ⟨u, hu⟩
        rcases v with ⟨v, hv⟩
        change op (A.obj i) ⟶ X at u
        change op (A.obj i) ⟶ Y at v
        change G.map u (tautologicalSection α i) = x at hu
        change G.map v (tautologicalSection α i) = y at hv
        subst x
        subst y
        apply heq_of_eq
        apply CategoryTheory.Over.OverMorphism.ext
        apply Quiver.Hom.unop_inj
        apply CategoryOfElements.ext
        rfl

omit [HasEqualizers C] [HasPullbacks C] in
private theorem liftSlice_project {A : FormalCoproduct.{w} C}
    (α : FormalCoproduct.toPresheaf.obj A ⟶ G) (i : A.I) :
    liftSlice α i ⋙ CategoryTheory.Over.post (Presheaf.localizationForget G) = 𝟭 _ := by
  fapply CategoryTheory.Functor.hext
  · rintro ⟨U, ⟨⟨⟩⟩, u⟩
    rfl
  · rintro ⟨U, ⟨⟨⟩⟩, u⟩ ⟨V, ⟨⟨⟩⟩, v⟩ f
    apply heq_of_eq
    apply CategoryTheory.Over.OverMorphism.ext
    rfl

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

private theorem localizedStage_inverse_laws (n : SimplexCategoryᵒᵖ) :
    (liftStage J K n ⋙ projectStage J K n = 𝟭 _) ∧
    (projectStage J K n ⋙ liftStage J K n = 𝟭 _) := by
  constructor
  · fapply CategoryTheory.Functor.hext
    · rintro ⟨i, U⟩
      exact congrArg (fun V ↦ (⟨i, V⟩ : OverSite (K.simplicial.obj n)))
        (CategoryTheory.Functor.congr_obj (liftSlice_project (K.augmentation.app n) i) U)
    · rintro ⟨i, U⟩ ⟨j, V⟩ ⟨g⟩
      exact CategoryTheory.Functor.postcomp_map_heq (overIncl (K.simplicial.obj n) i)
        (CategoryTheory.Functor.congr_obj (liftSlice_project (K.augmentation.app n) i) U)
        (CategoryTheory.Functor.congr_obj (liftSlice_project (K.augmentation.app n) i) _)
        (CategoryTheory.Functor.hcongr_hom (liftSlice_project (K.augmentation.app n) i) g)
  · fapply CategoryTheory.Functor.hext
    · rintro ⟨i, U⟩
      exact congrArg (fun V ↦ (⟨i, V⟩ : OverSite ((toLocalizedSimplicial J K).obj n)))
        (CategoryTheory.Functor.congr_obj (project_liftSlice (K.augmentation.app n) i) U)
    · rintro ⟨i, U⟩ ⟨j, V⟩ ⟨g⟩
      exact CategoryTheory.Functor.postcomp_map_heq
        (overIncl ((toLocalizedSimplicial J K).obj n) i)
        (CategoryTheory.Functor.congr_obj (project_liftSlice (K.augmentation.app n) i) U)
        (CategoryTheory.Functor.congr_obj (project_liftSlice (K.augmentation.app n) i) _)
        (CategoryTheory.Functor.hcongr_hom (project_liftSlice (K.augmentation.app n) i) g)

/-- Lifting slices by their tautological sections commutes with simplicial relocalization. -/
theorem toLocalizedTotalSite_laws {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (overSiteDiagram K.simplicial).map f ≫ (liftStage J K m).toCatHom =
      (liftStage J K n).toCatHom ≫ (overSiteDiagram (toLocalizedSimplicial J K)).map f := by
  apply Cat.ext
  change overMap (K.simplicial.map f) ⋙ liftStage J K m =
    liftStage J K n ⋙ overMap ((toLocalizedSimplicial J K).map f)
  have h : overMap ((toLocalizedSimplicial J K).map f) ⋙ projectStage J K m =
      projectStage J K n ⋙ overMap (K.simplicial.map f) := by
    fapply CategoryTheory.Functor.hext
    · rintro ⟨i, U⟩
      rfl
    · rintro ⟨i, U⟩ ⟨j, V⟩ ⟨g⟩
      rfl
  calc
    overMap (K.simplicial.map f) ⋙ liftStage J K m =
        (liftStage J K n ⋙ projectStage J K n) ⋙
          overMap (K.simplicial.map f) ⋙ liftStage J K m := by
      rw [(localizedStage_inverse_laws J K n).1]
      rfl
    _ = liftStage J K n ⋙
        (overMap ((toLocalizedSimplicial J K).map f) ⋙ projectStage J K m) ⋙
          liftStage J K m := by rw [h]; rfl
    _ = liftStage J K n ⋙ overMap ((toLocalizedSimplicial J K).map f) ⋙
        (projectStage J K m ⋙ liftStage J K m) := rfl
    _ = liftStage J K n ⋙ overMap ((toLocalizedSimplicial J K).map f) := by
      rw [(localizedStage_inverse_laws J K m).2]
      rfl

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
      (projectStage J K n).toCatHom ≫ (overSiteDiagram K.simplicial).map f := by
  apply Cat.ext
  fapply CategoryTheory.Functor.hext
  · rintro ⟨i, U⟩
    rfl
  · rintro ⟨i, U⟩ ⟨j, V⟩ ⟨g⟩
    rfl

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
    (fromLocalizedTotalSite J K ⋙ toLocalizedTotalSite J K = 𝟭 _) := by
  constructor
  · dsimp only [toLocalizedTotalSite, fromLocalizedTotalSite]
    rw [← Grothendieck.map_comp_eq]
    trans Grothendieck.map (𝟙 (overSiteDiagram K.simplicial))
    · congr 1
      ext n
      exact (localizedStage_inverse_laws J K n).1
    · exact Grothendieck.map_id_eq
  · dsimp only [toLocalizedTotalSite, fromLocalizedTotalSite]
    rw [← Grothendieck.map_comp_eq]
    trans Grothendieck.map (𝟙 (overSiteDiagram (toLocalizedSimplicial J K)))
    · congr 1
      ext n
      exact (localizedStage_inverse_laws J K n).2
    · exact Grothendieck.map_id_eq

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
