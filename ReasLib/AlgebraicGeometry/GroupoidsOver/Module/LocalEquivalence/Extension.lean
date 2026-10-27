/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Stackification
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Stackification.SmallCover
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.CategoryTheory.Sites.IsSheafFor

/-! # Compatible-section extension along local equivalences -/

@[expose] public section

set_option backward.privateInPublic true
set_option maxHeartbeats 1600000

open CategoryTheory Opposite FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.LocalEquivalenceModules

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable (f : X ⟶ Y) (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f)

/-- The essential-image cover of a target object. -/
private def localCover (y : Y.total) :
    (Scheme.fppfTopology.over S).Cover (Y.p.obj y) :=
  ⟨CartesianBasedFunctor.EssentialImage.sieve (toCartesianBasedFunctor f) ⟨y, rfl⟩,
    hf.2 ⟨y, rfl⟩⟩

/-- The native small fppf refinement of the essential-image cover. -/
private def refinement (y : Y.total) :=
  Stackification.smallRefinement (localCover f hf y)

/-- The index type of the selected lifting cover lies in the scheme universe. -/
private abbrev coverIndex (y : Y.total) : Type u := (refinement f hf y).Index

/-- Each member of the selected cover has a source-fibre model. -/
private def localModel (y : Y.total) (i : coverIndex f hf y) :
    X.p.Fiber ((refinement f hf y).object i) :=
  ((refinement f hf y).member i).choose

/-- The specified isomorphism from the source model to the reindexed target object. -/
private def localModelIso (y : Y.total) (i : coverIndex f hf y) :
    ((toCartesianBasedFunctor f).fiberFunctor ((refinement f hf y).object i)).obj
        (localModel f hf y i) ≅
      ((Functor.Cleavage.ofIsFibered Y.p).reindex ((refinement f hf y).arrow i)).obj
        ⟨y, rfl⟩ :=
  ((refinement f hf y).member i).choose_spec.some

/-- The selected model maps to the target object by its fibre isomorphism and cartesian lift. -/
private def localModelArrow (y : Y.total) (i : coverIndex f hf y) :
    (toFunctor f).obj (localModel f hf y i).1 ⟶ y :=
  (Functor.Fiber.fiberInclusion.map (localModelIso f hf y i).hom) ≫
    (Functor.Cleavage.ofIsFibered Y.p).cartesianHom
      ((refinement f hf y).arrow i) ⟨y, rfl⟩

/-- The selected model arrows lie over the small covering family and cover the target object. -/
private theorem localModel_spec (y : Y.total) :
    (∀ i : coverIndex f hf y,
      Y.p.IsHomLift ((refinement f hf y).arrow i) (localModelArrow f hf y i)) ∧
      Sieve.ofArrows (fun i ↦ (toFunctor f).obj (localModel f hf y i).1)
        (localModelArrow f hf y) ∈ Y.fppfTopology y := sorry

/-- Scalar restriction from a target object to a selected local source model. -/
private def localScalar (y : Y.total) (i : coverIndex f hf y) :
    (structureSheaf Y).obj.obj (op y) ⟶
      (structureSheaf X).obj.obj (op (localModel f hf y i).1) :=
  (structureSheaf Y).obj.map (localModelArrow f hf y i).op ≫
    (structureSheafIso f).hom.hom.app (op (localModel f hf y i).1)

/-- The local section module with scalars restricted from the target object. -/
private def localModule (F : SheafOfModules.{u} (structureSheaf X))
    (y : Y.total) (i : coverIndex f hf y) :
    _root_.ModuleCat.{u} ((structureSheaf Y).obj.obj (op y)) :=
  (_root_.ModuleCat.restrictScalars (localScalar f hf y i).hom).obj
    (F.val.obj (op (localModel f hf y i).1))

/-- Local sections match whenever their source restrictions map to the same target arrow. -/
private def Compatible (F : SheafOfModules.{u} (structureSheaf X)) (y : Y.total)
    (s : ∀ i : coverIndex f hf y, localModule f hf F y i) : Prop :=
  ∀ (i j : coverIndex f hf y) (z : X.total)
    (a : z ⟶ (localModel f hf y i).1) (b : z ⟶ (localModel f hf y j).1),
    (toFunctor f).map a ≫ localModelArrow f hf y i =
        (toFunctor f).map b ≫ localModelArrow f hf y j →
      F.val.map a.op (s i) = F.val.map b.op (s j)

/-- Matching local section families are closed under the componentwise module operations. -/
private theorem sections_laws (F : SheafOfModules.{u} (structureSheaf X)) (y : Y.total) :
    Compatible f hf F y 0 ∧
      (∀ s t, Compatible f hf F y s → Compatible f hf F y t →
        Compatible f hf F y (s + t)) ∧
      (∀ (r : (structureSheaf Y).obj.obj (op y)) s,
        Compatible f hf F y s → Compatible f hf F y (r • s)) := sorry

/-- Compatible local sections form a submodule of the product over a small fppf lifting cover. -/
def sections (F : SheafOfModules.{u} (structureSheaf X)) (y : Y.total) :
    Submodule ((structureSheaf Y).obj.obj (op y))
      (∀ i : coverIndex f hf y, localModule f hf F y i) where
  carrier := { s | Compatible f hf F y s }
  zero_mem' := (sections_laws f hf F y).1
  add_mem' := fun {s t} hs ht ↦ (sections_laws f hf F y).2.1 s t hs ht
  smul_mem' := (sections_laws f hf F y).2.2

/-- The underlying sheaf of sets of a supplied module sheaf. -/
private def underlyingSheaf (F : SheafOfModules.{u} (structureSheaf X)) :
    Sheaf X.fppfTopology (Type u) :=
  (sheafCompose X.fppfTopology (forget AddCommGrpCat.{u})).obj
    ⟨F.val.presheaf, F.isSheaf⟩

/-- The sieve on which a target arrow between source images admits a source lift. -/
private def liftedSectionSieve {x' x : X.total}
    (a : (toFunctor f).obj x' ⟶ (toFunctor f).obj x) : Sieve x' where
  arrows z k := ∃ l : z ⟶ x, (toFunctor f).map l = (toFunctor f).map k ≫ a
  downward_closed := fun {z w} k hk h ↦
    ⟨h ≫ hk.choose,
      ((toFunctor f).map_comp h hk.choose).trans
        ((congrArg (fun b ↦ (toFunctor f).map h ≫ b) hk.choose_spec).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun b ↦ b ≫ a) ((toFunctor f).map_comp h k).symm)))⟩

/-- On the lifting sieve, a section restricts along an admissible source lift. -/
private def liftedSectionFamily (F : SheafOfModules.{u} (structureSheaf X))
    {x' x : X.total} (a : (toFunctor f).obj x' ⟶ (toFunctor f).obj x)
    (s : F.val.obj (op x)) :
    Presieve.FamilyOfElements (underlyingSheaf F).obj (liftedSectionSieve f a).arrows :=
  fun _ _ hk ↦ F.val.map hk.choose.op s

include hf in
/-- The lifting sieve covers, the lifted restrictions match, and the restricted
value is independent of every admissible lift of the target arrow. -/
private theorem liftedSectionFamily_compatible
    (F : SheafOfModules.{u} (structureSheaf X)) {x' x : X.total}
    (a : (toFunctor f).obj x' ⟶ (toFunctor f).obj x) (s : F.val.obj (op x)) :
    liftedSectionSieve f a ∈ X.fppfTopology x' ∧
      (liftedSectionFamily f F a s).Compatible ∧
      (∀ (z : X.total) (k : z ⟶ x') (hk : liftedSectionSieve f a k)
        (l : z ⟶ x), (toFunctor f).map l = (toFunctor f).map k ≫ a →
          liftedSectionFamily f F a s k hk = F.val.map l.op s) := sorry

/-- A target arrow acts on source sections by gluing the locally lifted restrictions. -/
private def liftedSection (F : SheafOfModules.{u} (structureSheaf X))
    {x' x : X.total} (a : (toFunctor f).obj x' ⟶ (toFunctor f).obj x)
    (s : F.val.obj (op x)) : F.val.obj (op x') :=
  ((underlyingSheaf F).property.isSheafFor (liftedSectionSieve f a)
      (liftedSectionFamily_compatible f hf F a s).1).amalgamate
    (liftedSectionFamily f F a s) (liftedSectionFamily_compatible f hf F a s).2.1

/-- The sieve on a source object obtained by locally factoring a target arrow
through the selected lifting cover. -/
private def restrictionSieve (y : Y.total) (x : X.total)
    (a : (toFunctor f).obj x ⟶ y) : Sieve x where
  arrows z k := ∃ i : coverIndex f hf y, ∃ l : z ⟶ (localModel f hf y i).1,
    (toFunctor f).map l ≫ localModelArrow f hf y i = (toFunctor f).map k ≫ a
  downward_closed := fun {z w k} hk h ↦
    ⟨hk.choose, h ≫ hk.choose_spec.choose,
      ((congrArg (fun b ↦ b ≫ localModelArrow f hf y hk.choose)
          ((toFunctor f).map_comp h hk.choose_spec.choose)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun b ↦ (toFunctor f).map h ≫ b) hk.choose_spec.choose_spec).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun b ↦ b ≫ a) ((toFunctor f).map_comp h k).symm)))))⟩

/-- A compatible extension section restricts along the source lift of a local factorization. -/
private def restrictionFamily (F : SheafOfModules.{u} (structureSheaf X))
    (y : Y.total) (s : sections f hf F y) (x : X.total)
    (a : (toFunctor f).obj x ⟶ y) :
    Presieve.FamilyOfElements (underlyingSheaf F).obj (restrictionSieve f hf y x a).arrows :=
  fun _ _ hk ↦ F.val.map hk.choose_spec.choose.op (s.1 hk.choose)

/-- Factoring a target arrow locally through a lifting cover gives a covering,
matching family, independent of its admissible factorizations. -/
private theorem restrictionFamily_compatible (F : SheafOfModules.{u} (structureSheaf X))
    (y : Y.total) (s : sections f hf F y) (x : X.total)
    (a : (toFunctor f).obj x ⟶ y) :
    restrictionSieve f hf y x a ∈ X.fppfTopology x ∧
      (restrictionFamily f hf F y s x a).Compatible ∧
      (∀ (z : X.total) (k : z ⟶ x) (hk : restrictionSieve f hf y x a k)
        (i : coverIndex f hf y) (l : z ⟶ (localModel f hf y i).1),
        (toFunctor f).map l ≫ localModelArrow f hf y i = (toFunctor f).map k ≫ a →
          restrictionFamily f hf F y s x a k hk = F.val.map l.op (s.1 i)) := sorry

/-- Evaluation on a source object is the original module sheaf's unique local amalgamation. -/
private def sectionAt (F : SheafOfModules.{u} (structureSheaf X))
    (y : Y.total) (s : sections f hf F y) (x : X.total)
    (a : (toFunctor f).obj x ⟶ y) : F.val.obj (op x) :=
  ((underlyingSheaf F).property.isSheafFor (restrictionSieve f hf y x a)
    (restrictionFamily_compatible f hf F y s x a).1).amalgamate
      (restrictionFamily f hf F y s x a)
      (restrictionFamily_compatible f hf F y s x a).2.1

/-- Restriction of a compatible family is evaluated on the selected local
models of its new target. -/
private def restrictionFunction (F : SheafOfModules.{u} (structureSheaf X))
    {y' y : Y.total} (a : y' ⟶ y) (s : sections f hf F y) :
    ∀ i : coverIndex f hf y', localModule f hf F y' i :=
  fun i ↦ sectionAt f hf F y s (localModel f hf y' i).1
    (localModelArrow f hf y' i ≫ a)

/-- Restriction produces compatible families and is additive and semilinear
for the target structure-sheaf restriction. -/
private theorem restriction_laws (F : SheafOfModules.{u} (structureSheaf X))
    {y' y : Y.total} (a : y' ⟶ y) :
    (∀ s, Compatible f hf F y' (restrictionFunction f hf F a s)) ∧
      (∀ s t, restrictionFunction f hf F a (s + t) =
        restrictionFunction f hf F a s + restrictionFunction f hf F a t) ∧
      (∀ (r : (structureSheaf Y).obj.obj (op y)) s,
        restrictionFunction f hf F a (r • s) =
          ((structureSheaf Y).obj.map a.op) r • restrictionFunction f hf F a s) := sorry

/-- The semilinear module restriction defined by local amalgamation. -/
private def restrictionMap (F : SheafOfModules.{u} (structureSheaf X))
    {y' y : Y.total} (a : y' ⟶ y) :
    _root_.ModuleCat.of ((structureSheaf Y).obj.obj (op y)) (sections f hf F y) ⟶
      (_root_.ModuleCat.restrictScalars ((structureSheaf Y).obj.map a.op).hom).obj
        (_root_.ModuleCat.of ((structureSheaf Y).obj.obj (op y')) (sections f hf F y')) :=
  _root_.ModuleCat.ofHom (X := _root_.ModuleCat.of
      ((structureSheaf Y).obj.obj (op y)) (sections f hf F y))
    (Y := (_root_.ModuleCat.restrictScalars ((structureSheaf Y).obj.map a.op).hom).obj
      (_root_.ModuleCat.of ((structureSheaf Y).obj.obj (op y')) (sections f hf F y')))
    { toFun := fun s ↦ ⟨restrictionFunction f hf F a s, (restriction_laws f hf F a).1 s⟩
      map_add' := fun s t ↦ Subtype.ext ((restriction_laws f hf F a).2.1 s t)
      map_smul' := fun r s ↦ Subtype.ext ((restriction_laws f hf F a).2.2 r s) }

/-- The locally glued restriction maps satisfy the presheaf identity and composition laws. -/
private theorem extensionPresheaf_laws (F : SheafOfModules.{u} (structureSheaf X)) :
    (∀ y : Y.totalᵒᵖ, restrictionMap f hf F (𝟙 y).unop =
      (_root_.ModuleCat.restrictScalarsId' ((structureSheaf Y).obj.map (𝟙 y)).hom
        (congrArg RingCat.Hom.hom ((structureSheaf Y).obj.map_id y))).inv.app _) ∧
      (∀ {x y z : Y.totalᵒᵖ} (a : x ⟶ y) (b : y ⟶ z),
        restrictionMap f hf F (a ≫ b).unop =
          restrictionMap f hf F a.unop ≫
            (_root_.ModuleCat.restrictScalars ((structureSheaf Y).obj.map a).hom).map
              (restrictionMap f hf F b.unop) ≫
            (_root_.ModuleCat.restrictScalarsComp'
              ((structureSheaf Y).obj.map a).hom ((structureSheaf Y).obj.map b).hom
              ((structureSheaf Y).obj.map (a ≫ b)).hom
              (congrArg RingCat.Hom.hom ((structureSheaf Y).obj.map_comp a b))).inv.app _) := sorry

/-- The explicit compatible-section presheaf, with restrictions given by local gluing. -/
private def extensionPresheaf (F : SheafOfModules.{u} (structureSheaf X)) :
    PresheafOfModules.{u} (structureSheaf Y).obj where
  obj y := _root_.ModuleCat.of ((structureSheaf Y).obj.obj y) (sections f hf F y.unop)
  map a := restrictionMap f hf F a.unop
  map_id := (extensionPresheaf_laws f hf F).1
  map_comp := fun a b ↦ (extensionPresheaf_laws f hf F).2 a b

/-- Compatible-section extension satisfies fppf descent. -/
private theorem extension_isSheaf (F : SheafOfModules.{u} (structureSheaf X)) :
    Presheaf.IsSheaf Y.fppfTopology (extensionPresheaf f hf F).presheaf := sorry

/-- The extension sheaf whose sections are compatible families on the selected small covers. -/
private def extensionObj (F : SheafOfModules.{u} (structureSheaf X)) :
    SheafOfModules.{u} (structureSheaf Y) where
  val := extensionPresheaf f hf F
  isSheaf := extension_isSheaf f hf F

/-- A module morphism acts componentwise on compatible section families. -/
private def extensionMapFunction {F G : SheafOfModules.{u} (structureSheaf X)}
    (φ : F ⟶ G) (y : Y.total) (s : sections f hf F y) :
    ∀ i : coverIndex f hf y, localModule f hf G y i :=
  fun i ↦ φ.val.app (op (localModel f hf y i).1) (s.1 i)

/-- A componentwise module map, supplied with its matching condition, is linear. -/
private def extensionMapApp {F G : SheafOfModules.{u} (structureSheaf X)}
    (φ : F ⟶ G)
    (hc : ∀ y s, Compatible f hf G y (extensionMapFunction f hf φ y s))
    (y : Y.total) : (extensionObj f hf F).val.obj (op y) ⟶
      (extensionObj f hf G).val.obj (op y) :=
  _root_.ModuleCat.ofHom
    (X := (extensionObj f hf F).val.obj (op y))
    (Y := (extensionObj f hf G).val.obj (op y))
    { toFun := fun s ↦ ⟨extensionMapFunction f hf φ y s, hc y s⟩
      map_add' := fun s t ↦ Subtype.ext (funext (fun i ↦
        map_add (φ.val.app (op (localModel f hf y i).1)).hom (s.1 i) (t.1 i)))
      map_smul' := fun r s ↦ Subtype.ext (funext (fun i ↦
        map_smul ((_root_.ModuleCat.restrictScalars (localScalar f hf y i).hom).map
          (φ.val.app (op (localModel f hf y i).1))).hom r (s.1 i))) }

/-- Componentwise module maps preserve matching and commute with extension restrictions. -/
private theorem extensionMap_laws {F G : SheafOfModules.{u} (structureSheaf X)}
    (φ : F ⟶ G) :
    (∀ y s, Compatible f hf G y (extensionMapFunction f hf φ y s)) ∧
      (∀ hc {y' y : Y.totalᵒᵖ} (a : y' ⟶ y),
        (extensionObj f hf F).val.map a ≫
            (_root_.ModuleCat.restrictScalars ((structureSheaf Y).obj.map a).hom).map
              (extensionMapApp f hf φ hc y.unop) =
          extensionMapApp f hf φ hc y'.unop ≫ (extensionObj f hf G).val.map a) := sorry

/-- Extension of a module morphism acts on each local component by that morphism. -/
private def extensionMap {F G : SheafOfModules.{u} (structureSheaf X)} (φ : F ⟶ G) :
    extensionObj f hf F ⟶ extensionObj f hf G where
  val :=
    { app := fun y ↦ extensionMapApp f hf φ (extensionMap_laws f hf φ).1 y.unop
      naturality := fun a ↦ (extensionMap_laws f hf φ).2 _ a }

/-- Componentwise extension preserves identity maps and composition. -/
private theorem extensionFunctor_laws :
    (∀ F, extensionMap f hf (𝟙 F) = 𝟙 (extensionObj f hf F)) ∧
      (∀ {F G H : SheafOfModules.{u} (structureSheaf X)} (φ : F ⟶ G) (ψ : G ⟶ H),
        extensionMap f hf (φ ≫ ψ) = extensionMap f hf φ ≫ extensionMap f hf ψ) := sorry

/-- Module extension along a local equivalence is formed from compatible sections
on the selected small fppf lifting covers. -/
def extensionFunctor :
    SheafOfModules.{u} (structureSheaf X) ⥤ SheafOfModules.{u} (structureSheaf Y) where
  obj := extensionObj f hf
  map := extensionMap f hf
  map_id := (extensionFunctor_laws f hf).1
  map_comp := fun φ ψ ↦ (extensionFunctor_laws f hf).2 φ ψ

/-- Linearity and restriction compatibility for a family of section functions. -/
private def MapLaws {Z : GroupoidsOver S}
    (F G : SheafOfModules.{u} (structureSheaf Z))
    (q : ∀ x : Z.total, F.val.obj (op x) → G.val.obj (op x)) : Prop :=
  (∀ x s t, q x (s + t) = q x s + q x t) ∧
    (∀ x (r : (structureSheaf Z).obj.obj (op x)) s, q x (r • s) = r • q x s) ∧
    (∀ {x y : Z.total} (a : x ⟶ y) s,
      q x (F.val.map a.op s) = G.val.map a.op (q y s))

/-- Linear restriction-compatible section functions define a morphism of module sheaves. -/
private def mapOfLaws {Z : GroupoidsOver S}
    {F G : SheafOfModules.{u} (structureSheaf Z)}
    (q : ∀ x : Z.total, F.val.obj (op x) → G.val.obj (op x))
    (h : MapLaws F G q) : F ⟶ G where
  val :=
    { app := fun x ↦ _root_.ModuleCat.ofHom
        (X := F.val.obj x) (Y := G.val.obj x)
        { toFun := q x.unop
          map_add' := h.1 x.unop
          map_smul' := h.2.1 x.unop }
      naturality := fun a ↦ _root_.ModuleCat.hom_ext
        (LinearMap.ext (fun s ↦ h.2.2 a.unop s)) }

/-- The counit evaluates a compatible family on a source object by local amalgamation. -/
private def counitFunction (F : SheafOfModules.{u} (structureSheaf X))
    (x : X.total) (s : ((extensionFunctor f hf ⋙ modulePullback f).obj F).val.obj
      (op x)) :=
  sectionAt f hf F ((toFunctor f).obj x) s x (𝟙 _)

/-- The inverse counit restricts a source section along locally lifted model arrows. -/
private def counitInverseFamily (F : SheafOfModules.{u} (structureSheaf X))
    (x : X.total) (s : F.val.obj (op x)) :
    ∀ i : coverIndex f hf ((toFunctor f).obj x),
      localModule f hf F ((toFunctor f).obj x) i :=
  fun i ↦ liftedSection f hf F (localModelArrow f hf ((toFunctor f).obj x) i) s

/-- The unit restricts a target section to its selected local source models. -/
private def unitFamily (G : SheafOfModules.{u} (structureSheaf Y))
    (y : Y.total) (s : G.val.obj (op y)) :
    ∀ i : coverIndex f hf y, localModule f hf ((modulePullback f).obj G) y i :=
  fun i ↦ G.val.map (localModelArrow f hf y i).op s

/-- A compatible family of pulled-back target sections gives a family on the target cover. -/
private def unitInverseFamily (G : SheafOfModules.{u} (structureSheaf Y))
    (y : Y.total) (s : sections f hf ((modulePullback f).obj G) y) :
    Presieve.FamilyOfElements (underlyingSheaf G).obj
      (Sieve.ofArrows (fun i ↦ (toFunctor f).obj (localModel f hf y i).1)
        (localModelArrow f hf y)).arrows :=
  fun _ _ hk ↦ G.val.map (Sieve.ofArrows.h hk).op (s.1 (Sieve.ofArrows.i hk))

/-- Local evaluation recovers each selected component, the inverse-counit
families match, and the unit families admit the specified target amalgamation. -/
theorem extensionEvaluation_laws :
    (∀ (F : SheafOfModules.{u} (structureSheaf X)) (y : Y.total)
      (s : sections f hf F y) (i : coverIndex f hf y),
      sectionAt f hf F y s (localModel f hf y i).1 (localModelArrow f hf y i) = s.1 i) ∧
    (∀ (F : SheafOfModules.{u} (structureSheaf X)) (x : X.total) s,
      Compatible f hf F ((toFunctor f).obj x) (counitInverseFamily f hf F x s)) ∧
    (∀ (G : SheafOfModules.{u} (structureSheaf Y)) (y : Y.total) s,
      Compatible f hf ((modulePullback f).obj G) y (unitFamily f hf G y s)) ∧
    (∀ (G : SheafOfModules.{u} (structureSheaf Y)) (y : Y.total)
      (s : sections f hf ((modulePullback f).obj G) y),
      (unitInverseFamily f hf G y s).Compatible) := sorry

/-- Evaluation of an extended section on any source arrow is given by unique
amalgamation in the original source module sheaf. -/
def extensionEvaluation (F : SheafOfModules.{u} (structureSheaf X)) (y : Y.total)
    (s : ((extensionFunctor f hf).obj F).val.obj (op y)) (x : X.total)
    (a : (toFunctor f).obj x ⟶ y) : F.val.obj (op x) :=
  sectionAt f hf F y s x a

/-- Evaluation is uniquely determined by restriction to any covering family of
source arrows factoring through the selected local models. -/
theorem extension_independence (F : SheafOfModules.{u} (structureSheaf X))
    (y : Y.total) (s : sections f hf F y) (x : X.total)
    (a : (toFunctor f).obj x ⟶ y) (t : F.val.obj (op x))
    (ht : ∀ (z : X.total) (k : z ⟶ x) (i : coverIndex f hf y)
      (l : z ⟶ (localModel f hf y i).1),
      (toFunctor f).map l ≫ localModelArrow f hf y i = (toFunctor f).map k ≫ a →
        F.val.map k.op t = F.val.map l.op (s.1 i)) :
    t = extensionEvaluation f hf F y s x a := sorry

/-- The inverse counit is the compatible family of independently glued source restrictions. -/
private def counitInverseFunction (F : SheafOfModules.{u} (structureSheaf X))
    (x : X.total) (s : F.val.obj (op x)) :
    ((extensionFunctor f hf ⋙ modulePullback f).obj F).val.obj (op x) :=
  ⟨counitInverseFamily f hf F x s, (extensionEvaluation_laws f hf).2.1 F x s⟩

/-- The unit is the compatible family of target restriction maps. -/
private def unitFunction (G : SheafOfModules.{u} (structureSheaf Y))
    (y : Y.total) (s : G.val.obj (op y)) :
    ((modulePullback f ⋙ extensionFunctor f hf).obj G).val.obj (op y) :=
  ⟨unitFamily f hf G y s, (extensionEvaluation_laws f hf).2.2.1 G y s⟩

/-- The inverse unit amalgamates the compatible family in the original target sheaf. -/
private def unitInverseFunction (G : SheafOfModules.{u} (structureSheaf Y))
    (y : Y.total) (s : ((modulePullback f ⋙ extensionFunctor f hf).obj G).val.obj (op y)) :
    G.val.obj (op y) :=
  ((underlyingSheaf G).property.isSheafFor _ (localModel_spec f hf y).2).amalgamate
    (unitInverseFamily f hf G y s) ((extensionEvaluation_laws f hf).2.2.2 G y s)

/-- The unit restriction maps and their target-sheaf amalgamations are linear,
natural, and mutually inverse. -/
private theorem unitIso_laws :
    (∀ G, MapLaws G ((modulePullback f ⋙ extensionFunctor f hf).obj G)
      (unitFunction f hf G)) ∧
    (∀ G, MapLaws ((modulePullback f ⋙ extensionFunctor f hf).obj G) G
      (unitInverseFunction f hf G)) ∧
    (∀ G y s, unitInverseFunction f hf G y (unitFunction f hf G y s) = s) ∧
    (∀ G y s, unitFunction f hf G y (unitInverseFunction f hf G y s) = s) ∧
    (∀ {G H : SheafOfModules.{u} (structureSheaf Y)} (φ : G ⟶ H) y s,
      unitFunction f hf H y (φ.val.app (op y) s) =
        ((modulePullback f ⋙ extensionFunctor f hf).map φ).val.app (op y)
          (unitFunction f hf G y s)) := sorry

/-- The source evaluation maps and independently lifted restrictions are linear,
natural, and mutually inverse. -/
private theorem counitIso_laws :
    (∀ F, MapLaws ((extensionFunctor f hf ⋙ modulePullback f).obj F) F
      (counitFunction f hf F)) ∧
    (∀ F, MapLaws F ((extensionFunctor f hf ⋙ modulePullback f).obj F)
      (counitInverseFunction f hf F)) ∧
    (∀ F x s, counitInverseFunction f hf F x (counitFunction f hf F x s) = s) ∧
    (∀ F x s, counitFunction f hf F x (counitInverseFunction f hf F x s) = s) ∧
    (∀ {F G : SheafOfModules.{u} (structureSheaf X)} (φ : F ⟶ G) x s,
      counitFunction f hf G x
          (((extensionFunctor f hf ⋙ modulePullback f).map φ).val.app (op x) s) =
        φ.val.app (op x) (counitFunction f hf F x s)) := sorry

/-- Mutually inverse, linear restriction-compatible section functions give an isomorphism. -/
private def isoOfFunctions {Z : GroupoidsOver S}
    {F G : SheafOfModules.{u} (structureSheaf Z)}
    (q : ∀ x, F.val.obj (op x) → G.val.obj (op x))
    (r : ∀ x, G.val.obj (op x) → F.val.obj (op x))
    (hq : MapLaws F G q) (hr : MapLaws G F r)
    (hqr : ∀ x s, r x (q x s) = s) (hrq : ∀ x s, q x (r x s) = s) : F ≅ G where
  hom := mapOfLaws q hq
  inv := mapOfLaws r hr
  hom_inv_id := SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun x ↦
    _root_.ModuleCat.hom_ext (LinearMap.ext (hqr x.unop))))
  inv_hom_id := SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun x ↦
    _root_.ModuleCat.hom_ext (LinearMap.ext (hrq x.unop))))

/-- Restriction to the lifting cover and original-sheaf amalgamation identify
a target module with the extension of its pullback. -/
def unitIso : 𝟭 (SheafOfModules.{u} (structureSheaf Y)) ≅
    modulePullback f ⋙ extensionFunctor f hf :=
  NatIso.ofComponents
    (fun G ↦ isoOfFunctions (unitFunction f hf G) (unitInverseFunction f hf G)
      ((unitIso_laws f hf).1 G) ((unitIso_laws f hf).2.1 G)
      ((unitIso_laws f hf).2.2.1 G) ((unitIso_laws f hf).2.2.2.1 G))
    (fun φ ↦ SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun y ↦
      _root_.ModuleCat.hom_ext (LinearMap.ext ((unitIso_laws f hf).2.2.2.2 φ y.unop)))))

/-- Local source evaluation and independently lifted restrictions identify
the pullback of an extended module with the original module. -/
def counitIso : extensionFunctor f hf ⋙ modulePullback f ≅
    𝟭 (SheafOfModules.{u} (structureSheaf X)) :=
  NatIso.ofComponents
    (fun F ↦ isoOfFunctions (counitFunction f hf F) (counitInverseFunction f hf F)
      ((counitIso_laws f hf).1 F) ((counitIso_laws f hf).2.1 F)
      ((counitIso_laws f hf).2.2.1 F) ((counitIso_laws f hf).2.2.2.1 F))
    (fun φ ↦ SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun x ↦
      _root_.ModuleCat.hom_ext (LinearMap.ext ((counitIso_laws f hf).2.2.2.2 φ x.unop)))))

/-- Local restriction followed by local evaluation satisfies the triangle identity. -/
theorem moduleEquivalence_triangle (G : SheafOfModules.{u} (structureSheaf Y)) :
    (modulePullback f).map ((unitIso f hf).hom.app G) ≫
      (counitIso f hf).hom.app ((modulePullback f).obj G) = 𝟙 _ := sorry

/-- Module sheaves are invariant under a local equivalence, with inverse
given by compatible sections on the original-universe lifting covers. -/
def moduleEquivalence :
    SheafOfModules.{u} (structureSheaf Y) ≌ SheafOfModules.{u} (structureSheaf X) where
  functor := modulePullback f
  inverse := extensionFunctor f hf
  unitIso := unitIso f hf
  counitIso := counitIso f hf
  functor_unitIso_comp := moduleEquivalence_triangle f hf

/-- Compatible-section extension of a quasi-coherent module is quasi-coherent. -/
theorem extension_isQuasicoherent (F : SheafOfModules.{u} (structureSheaf X))
    (hF : F.IsQuasicoherent) : ((extensionFunctor f hf).obj F).IsQuasicoherent := sorry

/-- Quasi-coherent extension is the restriction of the concrete module-extension functor. -/
def qcohExtension : QCoh X ⥤ QCoh Y :=
  ObjectProperty.FullSubcategory.restrict (extensionFunctor f hf)
    (fun F hF ↦ extension_isQuasicoherent f hf F hF)

/-- Quasi-coherent module sheaves are invariant under a local equivalence,
with the actual pullback and compatible-section extension as its two functors. -/
def qcohEquivalence : QCoh Y ≌ QCoh X where
  functor := QCoh.pullback f
  inverse := qcohExtension f hf
  unitIso := NatIso.ofComponents
    (fun G ↦ ObjectProperty.isoMk _ ((unitIso f hf).app G.obj))
    (fun φ ↦ ObjectProperty.hom_ext _ ((unitIso f hf).hom.naturality φ.hom))
  counitIso := NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _ ((counitIso f hf).app F.obj))
    (fun φ ↦ ObjectProperty.hom_ext _ ((counitIso f hf).hom.naturality φ.hom))
  functor_unitIso_comp G := ObjectProperty.hom_ext _
    (moduleEquivalence_triangle f hf G.obj)

end AlgebraicGeometry.GroupoidsOver.LocalEquivalenceModules

