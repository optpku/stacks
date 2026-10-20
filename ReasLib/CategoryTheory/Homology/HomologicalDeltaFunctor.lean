module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homological Delta Functors

This module is the homological (lower-indexed) companion of
`CohomologicalDeltaFunctor`.  It is independent of resolutions and derived categories, so a
source can state universal homological comparisons before choosing a computational model.
-/

@[expose] public section

namespace CategoryTheory

open ComposableArrows

universe vA uA vB uB

/-- 010Q (homological form): a homological delta functor consists of additive degreewise functors,
connecting morphisms, the long-exactness window, and naturality for short exact sequences. -/
@[stacks 010Q "homological delta functor"]
structure HomologicalDeltaFunctor (A : Type uA) [Category.{vA} A] [Preadditive A]
    (B : Type uB) [Category.{vB} B] [Preadditive B] where
  /-- The additive functor in each homological degree. -/
  F : ℕ → A ⥤+ B
  /-- The connecting morphism from degree `n + 1` on the third term to degree `n` on the first. -/
  δ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ) :
    (F (n + 1)).obj.obj S.X₃ ⟶ (F n).obj.obj S.X₁
  /-- The degree-zero image of the quotient map of a short exact sequence is epic. -/
  epi_map_g_zero ⦃S : ShortComplex A⦄ (hS : S.ShortExact) : Epi ((F 0).obj.map S.g)
  /-- The standard five-arrow window in the induced long exact sequence is exact. -/
  exact₅ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ) :
    (mk₅ ((F (n + 1)).obj.map S.f) ((F (n + 1)).obj.map S.g) (δ hS n)
      ((F n).obj.map S.f) ((F n).obj.map S.g)).Exact
  /-- The connecting morphisms are natural in morphisms of short exact sequences. -/
  δ_naturality ⦃S T : ShortComplex A⦄ (hS : S.ShortExact) (hT : T.ShortExact)
      (φ : S ⟶ T) (n : ℕ) :
    CommSq ((F (n + 1)).obj.map φ.τ₃) (δ hS n) (δ hT n) ((F n).obj.map φ.τ₁)

namespace HomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]

/-- A homological delta functor coerces to its family of degreewise additive functors. -/
instance : CoeFun (HomologicalDeltaFunctor A B) (fun _ ↦ ℕ → A ⥤+ B) where
  coe T := T.F

/-- Exactness at the middle object after applying the degree-`n` functor. -/
theorem map_exact (F : HomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (S.map (F n).obj).Exact := sorry

/-- The image of the second map is annihilated by the connecting morphism. -/
@[simp, reassoc]
theorem map_g_comp_δ (F : HomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (F (n + 1)).obj.map S.g ≫ F.δ hS n = 0 := sorry

/-- Exactness at the third degree-`n + 1` term and the connecting morphism. -/
theorem exact_map_g_δ (F : HomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk ((F (n + 1)).obj.map S.g) (F.δ hS n) (F.map_g_comp_δ hS n)).Exact := sorry

/-- The connecting morphism is annihilated by the next first map. -/
@[simp, reassoc]
theorem δ_comp_map_f (F : HomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    F.δ hS n ≫ (F n).obj.map S.f = 0 := sorry

/-- The connecting morphism of a split short exact sequence vanishes when the first map
admits a retraction. -/
theorem δ_eq_zero_of_retraction (F : HomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (r : S.X₂ ⟶ S.X₁) (hr : S.f ≫ r = 𝟙 S.X₁) (n : ℕ) :
    F.δ hS n = 0 := sorry

/-- Exactness at the degree-`n` first term after the connecting morphism. -/
theorem exact_δ_map_f (F : HomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (F.δ hS n) ((F n).obj.map S.f) (F.δ_comp_map_f hS n)).Exact := sorry

/-- Assemble the five-arrow long-exactness window from adjacent exactness statements. -/
theorem exact₅_of_adjacent_exactness
    {F : ℕ → A ⥤+ B}
    {δ : ∀ ⦃S : ShortComplex A⦄ (_hS : S.ShortExact) (n : ℕ),
      (F (n + 1)).obj.obj S.X₃ ⟶ (F n).obj.obj S.X₁}
    (map_g_comp_δ : ∀ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ),
      (F (n + 1)).obj.map S.g ≫ δ hS n = 0)
    (δ_comp_map_f : ∀ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ),
      δ hS n ≫ (F n).obj.map S.f = 0)
    (map_exact : ∀ ⦃S : ShortComplex A⦄ (_hS : S.ShortExact) (n : ℕ),
      (S.map (F n).obj).Exact)
    (exact_map_g_δ : ∀ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ),
      (ShortComplex.mk ((F (n + 1)).obj.map S.g) (δ hS n) (map_g_comp_δ hS n)).Exact)
    (exact_δ_map_f : ∀ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ),
      (ShortComplex.mk (δ hS n) ((F n).obj.map S.f) (δ_comp_map_f hS n)).Exact)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (mk₅ ((F (n + 1)).obj.map S.f) ((F (n + 1)).obj.map S.g) (δ hS n)
      ((F n).obj.map S.f) ((F n).obj.map S.g)).Exact := sorry

/-- A morphism of homological delta functors is degreewise natural and connecting-compatible. -/
@[ext, stacks 010R "morphism of homological delta functors"]
structure Hom (F G : HomologicalDeltaFunctor A B) where
  /-- The degreewise natural transformations. -/
  app (n : ℕ) : (F n).obj ⟶ (G n).obj
  /-- Compatibility with connecting morphisms. -/
  comm ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ) :
    CommSq ((app (n + 1)).app S.X₃) (F.δ hS n) (G.δ hS n) ((app n).app S.X₁)

namespace Hom

/-- The identity morphism of a homological delta functor. -/
def id (F : HomologicalDeltaFunctor A B) : Hom F F where
  app n := 𝟙 ((F n).obj)
  comm := sorry

/-- Composition of morphisms of homological delta functors. -/
def comp {F G H : HomologicalDeltaFunctor A B} (τ : Hom F G) (σ : Hom G H) : Hom F H where
  app n := τ.app n ≫ σ.app n
  comm := sorry

end Hom

/-- Homological delta functors form a category under degreewise composition. -/
instance : Category (HomologicalDeltaFunctor A B) where
  Hom F G := Hom F G
  id := Hom.id
  comp τ σ := Hom.comp τ σ
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The degreewise component of the identity morphism. -/
@[simp]
theorem id_app (F : HomologicalDeltaFunctor A B) (n : ℕ) :
    (𝟙 F : F ⟶ F).app n = 𝟙 ((F n).obj) := sorry

/-- The degreewise component of a composite of morphisms. -/
@[simp]
theorem comp_app {F G H : HomologicalDeltaFunctor A B} (τ : F ⟶ G) (σ : G ⟶ H)
    (n : ℕ) :
    (τ ≫ σ).app n = τ.app n ≫ σ.app n := sorry

/-- A homological delta functor is universal when degree-zero maps into it extend uniquely. -/
@[stacks 010S "universal homological delta functor"]
class IsUniversal (F : HomologicalDeltaFunctor A B) : Prop where
  /-- Every degree-zero map into this functor extends uniquely to all degrees. -/
  existsUnique_hom (G : HomologicalDeltaFunctor A B) (t : (G 0).obj ⟶ (F 0).obj) :
    ∃! τ : G ⟶ F, τ.app 0 = t

namespace IsUniversal

/-- A morphism into a universal homological delta functor is determined in degree zero. -/
theorem hom_ext
    {F G : HomologicalDeltaFunctor A B} [IsUniversal G]
    {τ σ : F ⟶ G} (h : τ.app 0 = σ.app 0) :
    τ = σ := sorry

/-- An isomorphism into a universal homological delta functor is determined by its
degree-zero component. -/
theorem iso_ext
    {F G : HomologicalDeltaFunctor A B} [IsUniversal G]
    {e e' : F ≅ G} (h : e.hom.app 0 = e'.hom.app 0) :
    e = e' := sorry

/-- Universal homological delta functors with a common degree-zero term are uniquely isomorphic. -/
@[stacks 010U "universal homological delta functor comparison"]
theorem uniqueIso
    {F : A ⥤ B}
    {G H : HomologicalDeltaFunctor A B}
    [IsUniversal G] [IsUniversal H]
    (eG : (G 0).obj ≅ F) (eH : (H 0).obj ≅ F) :
    ∃! e : G ≅ H, e.hom.app 0 = eG.hom ≫ eH.inv := sorry

/-- Universal homological delta functors are uniquely isomorphic once their degree-zero
comparison is an isomorphism. -/
theorem uniqueIso_of_isIso
    {G H : HomologicalDeltaFunctor A B}
    [IsUniversal G] [IsUniversal H]
    (t : (G 0).obj ⟶ (H 0).obj) (ht : IsIso t) :
    ∃! e : G ≅ H, e.hom.app 0 = t := sorry

end IsUniversal

end HomologicalDeltaFunctor

end CategoryTheory
