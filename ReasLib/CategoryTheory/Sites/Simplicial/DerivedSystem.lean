/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.ExactMorphismOfSites

/-!
# Simplicial systems of derived abelian sheaves

Objects and inverse-image transitions are compatible with composition through
comparison isomorphisms of exact inverse-image functors.  The inverse images
are anchored to a diagram of sites, and their comparisons satisfy the unit
and associativity laws.  Stacks Situation 85.3.3 is recovered by the canonical
contexts in the restriction and Grothendieck facades.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Functor

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable {C : SimplexCategory → Type u} [∀ n, Category.{v} (C n)]
variable (J : ∀ n, GrothendieckTopology (C n))
variable (fInv : ∀ {m n : SimplexCategory}, (m ⟶ n) →
    Sheaf (J m) AddCommGrpCat.{w} ⥤ Sheaf (J n) AddCommGrpCat.{w})
variable [∀ n, HasSheafify (J n) AddCommGrpCat.{w}]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), (fInv φ).Additive]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), PreservesFiniteLimits (fInv φ)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), PreservesFiniteColimits (fInv φ)]

/-- The inverse-image functor presented by a continuous functor of sites.  The
left Kan extensions are kept as an explicit proposition so that this
presentation does not manufacture any functorial data by choice. -/
noncomputable def continuousSiteInverseImage
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) (hu : u.IsContinuous J K)
    (hKan : ∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension P)
    [HasWeakSheafify K AddCommGrpCat.{w}] :
    Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w} := by
  letI : u.IsContinuous J K := hu
  letI : ∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension P := hKan
  exact u.sheafPullback AddCommGrpCat.{w} J K

/-- The inverse-image functor presented by a cocontinuous functor of sites. -/
noncomputable def cocontinuousSiteInverseImage
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (u : C ⥤ D) [HasWeakSheafify J AddCommGrpCat.{w}] :
    Sheaf K AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w} :=
  u.sheafPullbackCocontinuous AddCommGrpCat.{w} J K

/-- The abelian inverse images are induced by a genuine diagram of site
functors, in either variance used in Stacks Situation 85.3.3.  Strict identity
and composition equations give the site diagram; equalities identify its
canonical abelian inverse images with the supplied functors.  Property `P`
is needed for the total site, and belongs to the case-B facade. -/
def IsAnchoredInverseImage : Prop :=
  (∃ (u : ∀ {m n : SimplexCategory}, (m ⟶ n) → C m ⥤ C n)
      (hcont : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        (u φ).IsContinuous (J m) (J n))
      (hKan : ∀ {m n : SimplexCategory} (φ : m ⟶ n)
        (P : (C m)ᵒᵖ ⥤ AddCommGrpCat.{w}), (u φ).op.HasLeftKanExtension P),
    (∀ n : SimplexCategory, u (𝟙 n) = 𝟭 (C n)) ∧
    (∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      u (ψ ≫ φ) = u ψ ⋙ u φ) ∧
    (∀ {m n : SimplexCategory} (φ : m ⟶ n),
      fInv φ = continuousSiteInverseImage.{u, v, w}
        (J m) (J n) (u φ) (hcont φ) (hKan φ)) ∧
    (∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ∃ (hWeak : HasWeakSheafify (J n) (Type w))
        (hKanType : ∀ P : (C m)ᵒᵖ ⥤ Type w, (u φ).op.HasLeftKanExtension P),
        @IsExactMorphismOfSites _ _ _ _ (J m) (J n) (u φ) hWeak hKanType)) ∨
  (∃ (u : ∀ {m n : SimplexCategory}, (m ⟶ n) → C n ⥤ C m),
    (∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (u φ).IsCocontinuous (J n) (J m)) ∧
    (∀ n : SimplexCategory, u (𝟙 n) = 𝟭 (C n)) ∧
    (∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      u (ψ ≫ φ) = u φ ⋙ u ψ) ∧
    (∀ {m n : SimplexCategory} (φ : m ⟶ n),
      fInv φ = cocontinuousSiteInverseImage.{u, v, w} (J n) (J m) (u φ)))

variable (compIso : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
    fInv (ψ ≫ φ) ≅ fInv ψ ⋙ fInv φ)

/-- Unit compatibility for the compositor. -/
def IsUnital
    {C : SimplexCategory → Type u} [∀ n, Category.{v} (C n)]
    (J : ∀ n, GrothendieckTopology (C n))
    (fInv : ∀ {m n : SimplexCategory}, (m ⟶ n) →
      Sheaf (J m) AddCommGrpCat.{w} ⥤ Sheaf (J n) AddCommGrpCat.{w})
    (compIso : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      fInv (ψ ≫ φ) ≅ fInv ψ ⋙ fInv φ) : Prop :=
  ∃ (unitIso : ∀ n : SimplexCategory,
      fInv (𝟙 n) ≅ 𝟭 (Sheaf (J n) AddCommGrpCat.{w})),
    (∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (eqToIso (congrArg fInv (Category.id_comp φ))).inv ≫
          (compIso (𝟙 m) φ).hom ≫
          whiskerRight (unitIso m).hom (fInv φ) ≫
          (Functor.leftUnitor (fInv φ)).hom = 𝟙 (fInv φ)) ∧
    (∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (eqToIso (congrArg fInv (Category.comp_id φ))).inv ≫
          (compIso φ (𝟙 n)).hom ≫
          whiskerLeft (fInv φ) (unitIso n).hom ≫
          (Functor.rightUnitor (fInv φ)).hom = 𝟙 (fInv φ))

/-- Associativity/pentagon compatibility for the compositor. -/
def IsAssociative
    {C : SimplexCategory → Type u} [∀ n, Category.{v} (C n)]
    (J : ∀ n, GrothendieckTopology (C n))
    (fInv : ∀ {m n : SimplexCategory}, (m ⟶ n) →
      Sheaf (J m) AddCommGrpCat.{w} ⥤ Sheaf (J n) AddCommGrpCat.{w})
    (compIso : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      fInv (ψ ≫ φ) ≅ fInv ψ ⋙ fInv φ) : Prop :=
  ∀ {k l m n : SimplexCategory} (ψ : k ⟶ l) (φ : l ⟶ m) (χ : m ⟶ n),
    (compIso (ψ ≫ φ) χ).hom ≫
        whiskerRight (compIso ψ φ).hom (fInv χ) ≫
        (Functor.associator (fInv ψ) (fInv φ) (fInv χ)).hom =
      (eqToIso (congrArg fInv (Category.assoc ψ φ χ))).hom ≫
        (compIso ψ (φ ≫ χ)).hom ≫
        whiskerLeft (fInv ψ) (compIso φ χ).hom

/-- Proof-only context for an anchored family of inverse images with coherent
composition comparisons.  Its data remain the explicit parameters `J`,
`fInv`, and `compIso`; no inverse-image functor is extracted by choice. -/
class IsInverseImageContext : Prop where
  /-- The functors are the canonical inverse images of a site diagram. -/
  anchored : IsAnchoredInverseImage J fInv
  /-- The compositor has a unit comparison satisfying both unit laws. -/
  unital : IsUnital J fInv compIso
  /-- The compositor satisfies the associativity/pentagon equation. -/
  associative : IsAssociative J fInv compIso

/-- An inverse-image composition comparison induces the comparison between
the derived inverse image of a composite and the iterated derived inverse images. -/
def derivedInverseImageCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (hcomp : fInv (ψ ≫ φ) ≅ fInv ψ ⋙ fInv φ) :
    (fInv (ψ ≫ φ)).mapDerivedCategory ≅
      (fInv ψ).mapDerivedCategory ⋙ (fInv φ).mapDerivedCategory :=
  Functor.MapDerivedCategory.functorIso hcomp ≪≫
    ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (fInv ψ)) (ExactFunctor.of (fInv φ))

/-- A simplicial derived system consists of derived abelian sheaves in every
degree and inverse-image transitions compatible with composition. -/
structure DerivedSystem where
  /-- The anchored site/inverse-image and pseudo-functor coherence context. -/
  context : IsInverseImageContext J fInv compIso
  /-- The derived abelian sheaf in each degree. -/
  obj : ∀ n : SimplexCategory, DerivedCategory (Sheaf (J n) AddCommGrpCat.{w})
  /-- The transition along a simplex operator. -/
  map : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (fInv φ).mapDerivedCategory.obj (obj m) ⟶ obj n
  /-- Transitions respect composition under the derived inverse-image comparison. -/
  map_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
    map (ψ ≫ φ) =
      (derivedInverseImageCompIso J fInv ψ φ (compIso ψ φ)).hom.app (obj l) ≫
        (fInv φ).mapDerivedCategory.map (map ψ) ≫ map φ

namespace DerivedSystem

variable {J fInv compIso}

/-- Construct a simplicial derived system in an anchored inverse-image context
from objects and composition-compatible transitions. -/
def of (context : IsInverseImageContext J fInv compIso)
    (obj : ∀ n : SimplexCategory, DerivedCategory (Sheaf (J n) AddCommGrpCat.{w}))
    (map : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (fInv φ).mapDerivedCategory.obj (obj m) ⟶ obj n)
    (map_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      map (ψ ≫ φ) =
        (derivedInverseImageCompIso J fInv ψ φ (compIso ψ φ)).hom.app (obj l) ≫
          (fInv φ).mapDerivedCategory.map (map ψ) ≫ map φ) :
    DerivedSystem J fInv compIso where
  context := context
  obj := obj
  map := map
  map_comp := map_comp

/-- The transitions of a simplicial derived system satisfy composition compatibility. -/
theorem spec (K : DerivedSystem J fInv compIso) :
    ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      K.map (ψ ≫ φ) =
        (derivedInverseImageCompIso J fInv ψ φ (compIso ψ φ)).hom.app (K.obj l) ≫
          (fInv φ).mapDerivedCategory.map (K.map ψ) ≫ K.map φ := sorry

/-- The objects of a system constructed from explicit data are the supplied objects. -/
theorem of_obj
    (context : IsInverseImageContext J fInv compIso)
    (obj : ∀ n : SimplexCategory, DerivedCategory (Sheaf (J n) AddCommGrpCat.{w}))
    (map : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (fInv φ).mapDerivedCategory.obj (obj m) ⟶ obj n)
    (map_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      map (ψ ≫ φ) =
        (derivedInverseImageCompIso J fInv ψ φ (compIso ψ φ)).hom.app (obj l) ≫
          (fInv φ).mapDerivedCategory.map (map ψ) ≫ map φ)
    (n : SimplexCategory) :
    (of context obj map map_comp).obj n = obj n := sorry

/-- The transitions of a system constructed from explicit data are the supplied maps. -/
theorem of_map
    (context : IsInverseImageContext J fInv compIso)
    (obj : ∀ n : SimplexCategory, DerivedCategory (Sheaf (J n) AddCommGrpCat.{w}))
    (map : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (fInv φ).mapDerivedCategory.obj (obj m) ⟶ obj n)
    (map_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      map (ψ ≫ φ) =
        (derivedInverseImageCompIso J fInv ψ φ (compIso ψ φ)).hom.app (obj l) ≫
          (fInv φ).mapDerivedCategory.map (map ψ) ≫ map φ)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (of context obj map map_comp).map φ = map φ := sorry

/-- A morphism of simplicial derived systems is a stagewise family commuting with transitions. -/
structure Hom (K L : DerivedSystem J fInv compIso) where
  /-- The component map in each degree. -/
  app : ∀ n : SimplexCategory, K.obj n ⟶ L.obj n
  /-- Components commute with each inverse-image transition. -/
  naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    K.map φ ≫ app n = (fInv φ).mapDerivedCategory.map (app m) ≫ L.map φ

/-- Construct a morphism of derived systems from components commuting with transitions. -/
def homMk {K L : DerivedSystem J fInv compIso}
    (app : ∀ n : SimplexCategory, K.obj n ⟶ L.obj n)
    (naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      K.map φ ≫ app n = (fInv φ).mapDerivedCategory.map (app m) ≫ L.map φ) :
    Hom K L where
  app := app
  naturality := naturality

/-- Components of a morphism constructed from explicit data are the supplied components. -/
theorem homMk_app {K L : DerivedSystem J fInv compIso}
    (app : ∀ n : SimplexCategory, K.obj n ⟶ L.obj n)
    (naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      K.map φ ≫ app n = (fInv φ).mapDerivedCategory.map (app m) ≫ L.map φ)
    (n : SimplexCategory) :
    (homMk app naturality).app n = app n := sorry

/-- Identity components commute with all transitions of a derived system. -/
theorem Hom.id_naturality (K : DerivedSystem J fInv compIso) :
    ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      K.map φ ≫ 𝟙 (K.obj n) =
        (fInv φ).mapDerivedCategory.map (𝟙 (K.obj m)) ≫ K.map φ := sorry

/-- The identity morphism of a derived system has identity components. -/
def Hom.id (K : DerivedSystem J fInv compIso) : Hom K K :=
  homMk (fun n ↦ 𝟙 (K.obj n)) (Hom.id_naturality K)

/-- Composites of transition-compatible families remain transition-compatible. -/
theorem Hom.comp_naturality {K L M : DerivedSystem J fInv compIso}
    (α : Hom K L) (β : Hom L M) :
    ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      K.map φ ≫ (α.app n ≫ β.app n) =
        (fInv φ).mapDerivedCategory.map (α.app m ≫ β.app m) ≫ M.map φ := sorry

/-- Composition of derived-system morphisms is stagewise composition. -/
def Hom.comp {K L M : DerivedSystem J fInv compIso}
    (α : Hom K L) (β : Hom L M) : Hom K M :=
  homMk (fun n ↦ α.app n ≫ β.app n) (Hom.comp_naturality α β)

/-- A derived system is cartesian when every transition is an isomorphism. -/
def IsCartesian (K : DerivedSystem J fInv compIso) : Prop :=
  ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (K.map φ)

/-- Cartesianness is equivalent to invertibility of every transition. -/
theorem isCartesian_iff (K : DerivedSystem J fInv compIso) :
    IsCartesian K ↔ ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (K.map φ) := sorry

end DerivedSystem

end CategoryTheory.SimplicialSites
