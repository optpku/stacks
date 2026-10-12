/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomological Delta Functors

This module owns the general category-theoretic interface for cohomological
delta functors.  It is formulated for preadditive categories and short exact
sequences, independently of the derived-category or sheaf-theoretic settings
that supply such functors.
-/

@[expose] public section

namespace CategoryTheory

open ComposableArrows

universe vA uA vB uB

/-- A cohomological delta functor from `A` to `B` consists of additive degreewise
functors, connecting morphisms on short exact
sequences, and the associated long-exactness and naturality data. -/
@[stacks 010Q]
structure CohomologicalDeltaFunctor (A : Type uA) [Category.{vA} A] [Preadditive A]
    (B : Type uB) [Category.{vB} B] [Preadditive B] where
  /-- The additive functor in each nonnegative degree. -/
  F : ℕ → A ⥤+ B
  /-- The connecting morphism associated to a short exact sequence in degree `n`. -/
  δ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ) :
    (F n).obj.obj S.X₃ ⟶ (F (n + 1)).obj.obj S.X₁
  /-- The degree-zero image of the first map of a short exact sequence is monic. -/
  mono_map_f_zero ⦃S : ShortComplex A⦄ (hS : S.ShortExact) : Mono ((F 0).obj.map S.f)
  /-- The standard five-arrow window in the induced long exact sequence is exact. -/
  exact₅ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ) :
    (mk₅ ((F n).obj.map S.f) ((F n).obj.map S.g) (δ hS n)
      ((F (n + 1)).obj.map S.f) ((F (n + 1)).obj.map S.g)).Exact
  /-- The connecting morphisms are natural in morphisms of short exact sequences. -/
  δ_naturality ⦃S T : ShortComplex A⦄ (hS : S.ShortExact) (hT : T.ShortExact)
      (φ : S ⟶ T) (n : ℕ) :
    CommSq ((F n).obj.map φ.τ₃) (δ hS n) (δ hT n) ((F (n + 1)).obj.map φ.τ₁)

namespace CohomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]

/-- Exactness at the middle object after applying the degree-`n` functor. -/
theorem map_exact (F : CohomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (S.map (F.F n).obj).Exact := sorry

/-- The image of the second map is annihilated by the connecting morphism. -/
@[simp, reassoc]
theorem map_g_comp_δ (F : CohomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (F.F n).obj.map S.g ≫ F.δ hS n = 0 := sorry

/-- Exactness at the third degree-`n` term and the connecting morphism. -/
theorem exact_map_g_δ (F : CohomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk ((F.F n).obj.map S.g) (F.δ hS n) (F.map_g_comp_δ hS n)).Exact := sorry

/-- The connecting morphism is annihilated by the next first map. -/
@[simp, reassoc]
theorem δ_comp_map_f (F : CohomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    F.δ hS n ≫ (F.F (n + 1)).obj.map S.f = 0 := sorry

/-- Exactness at the next first term after the connecting morphism. -/
theorem exact_δ_map_f (F : CohomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (F.δ hS n) ((F.F (n + 1)).obj.map S.f)
      (F.δ_comp_map_f hS n)).Exact := sorry

/-- The connecting morphism of a split short exact sequence vanishes. -/
theorem δ_eq_zero_of_section (F : CohomologicalDeltaFunctor A B) {S : ShortComplex A}
    (hS : S.ShortExact) (s : S.X₃ ⟶ S.X₂) (hs : s ≫ S.g = 𝟙 S.X₃) (n : ℕ) :
    F.δ hS n = 0 := sorry

/-- Assemble the five-arrow long-exactness window from its adjacent exactness pieces. -/
theorem exact₅_of_adjacent_exactness
    {F : ℕ → A ⥤+ B}
    {δ : ∀ ⦃S : ShortComplex A⦄ (_hS : S.ShortExact) (n : ℕ),
      (F n).obj.obj S.X₃ ⟶ (F (n + 1)).obj.obj S.X₁}
    (map_g_comp_δ : ∀ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ),
      (F n).obj.map S.g ≫ δ hS n = 0)
    (δ_comp_map_f : ∀ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ),
      δ hS n ≫ (F (n + 1)).obj.map S.f = 0)
    (map_exact : ∀ ⦃S : ShortComplex A⦄ (_hS : S.ShortExact) (n : ℕ), (S.map (F n).obj).Exact)
    (exact_map_g_δ : ∀ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ),
      (ShortComplex.mk ((F n).obj.map S.g) (δ hS n) (map_g_comp_δ hS n)).Exact)
    (exact_δ_map_f : ∀ ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ),
      (ShortComplex.mk (δ hS n) ((F (n + 1)).obj.map S.f) (δ_comp_map_f hS n)).Exact)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (mk₅ ((F n).obj.map S.f) ((F n).obj.map S.g) (δ hS n)
      ((F (n + 1)).obj.map S.f) ((F (n + 1)).obj.map S.g)).Exact := sorry

/-- A morphism of cohomological delta functors is a family of degreewise natural
transformations compatible with all connecting morphisms. -/
@[ext, stacks 010R]
structure Hom (F G : CohomologicalDeltaFunctor A B) where
  /-- The degreewise natural transformations. -/
  app (n : ℕ) : (F.F n).obj ⟶ (G.F n).obj
  /-- Compatibility of the degreewise transformations with connecting morphisms. -/
  comm ⦃S : ShortComplex A⦄ (hS : S.ShortExact) (n : ℕ) :
    CommSq ((app n).app S.X₃) (F.δ hS n) (G.δ hS n) ((app (n + 1)).app S.X₁)

namespace Hom

/-- The identity morphism of a cohomological delta functor. -/
def id (F : CohomologicalDeltaFunctor A B) : Hom F F where
  app n := 𝟙 ((F.F n).obj)
  comm := sorry

/-- Composition of morphisms of cohomological delta functors. -/
def comp {F G H : CohomologicalDeltaFunctor A B} (τ : Hom F G) (σ : Hom G H) : Hom F H where
  app n := τ.app n ≫ σ.app n
  comm := sorry


/-- Left composition with the identity morphism does not change a morphism of
cohomological delta functors. -/
@[simp]
theorem id_comp {F G : CohomologicalDeltaFunctor A B} (τ : Hom F G) :
    comp (id F) τ = τ := sorry

/-- Right composition with the identity morphism does not change a morphism of
cohomological delta functors. -/
@[simp]
theorem comp_id {F G : CohomologicalDeltaFunctor A B} (τ : Hom F G) :
    comp τ (id G) = τ := sorry

/-- Composition of morphisms of cohomological delta functors is associative. -/
theorem assoc {F G H I : CohomologicalDeltaFunctor A B}
    (τ : Hom F G) (σ : Hom G H) (υ : Hom H I) :
    comp (comp τ σ) υ = comp τ (comp σ υ) := sorry

end Hom

/-- The degreewise component of the identity morphism. -/
@[simp]
theorem id_app (F : CohomologicalDeltaFunctor A B) (n : ℕ) :
    (Hom.id F).app n = 𝟙 ((F.F n).obj) := sorry

/-- The degreewise component of a composite of morphisms. -/
@[simp]
theorem comp_app {F G H : CohomologicalDeltaFunctor A B} (τ : Hom F G) (σ : Hom G H)
    (n : ℕ) :
    (Hom.comp τ σ).app n = τ.app n ≫ σ.app n := sorry

/-- An explicit isomorphism of cohomological delta functors consists of mutually inverse
morphisms of cohomological delta functors. -/
@[ext]
structure HomIso (F G : CohomologicalDeltaFunctor A B) where
  /-- The forward morphism. -/
  hom : Hom F G
  /-- The inverse morphism. -/
  inv : Hom G F
  /-- The forward morphism followed by the inverse is the identity. -/
  hom_inv_id : Hom.comp hom inv = Hom.id F
  /-- The inverse followed by the forward morphism is the identity. -/
  inv_hom_id : Hom.comp inv hom = Hom.id G

namespace HomIso

/-- The identity isomorphism of a cohomological delta functor. -/
def refl (F : CohomologicalDeltaFunctor A B) : HomIso F F where
  hom := Hom.id F
  inv := Hom.id F
  hom_inv_id := Hom.id_comp (Hom.id F)
  inv_hom_id := Hom.id_comp (Hom.id F)

/-- The inverse of an explicit isomorphism of cohomological delta functors. -/
def symm {F G : CohomologicalDeltaFunctor A B} (e : HomIso F G) : HomIso G F where
  hom := e.inv
  inv := e.hom
  hom_inv_id := e.inv_hom_id
  inv_hom_id := e.hom_inv_id

/-- The composite of explicit isomorphisms of cohomological delta functors. -/
def trans {F G H : CohomologicalDeltaFunctor A B}
    (e : HomIso F G) (e' : HomIso G H) : HomIso F H where
  hom := Hom.comp e.hom e'.hom
  inv := Hom.comp e'.inv e.inv
  hom_inv_id := by
    calc
      Hom.comp (Hom.comp e.hom e'.hom) (Hom.comp e'.inv e.inv) =
          Hom.comp e.hom (Hom.comp e'.hom (Hom.comp e'.inv e.inv)) :=
        Hom.assoc e.hom e'.hom (Hom.comp e'.inv e.inv)
      _ = Hom.comp e.hom (Hom.comp (Hom.comp e'.hom e'.inv) e.inv) := by
        rw [Hom.assoc e'.hom e'.inv e.inv]
      _ = Hom.comp e.hom e.inv := by rw [e'.hom_inv_id, Hom.id_comp]
      _ = Hom.id F := e.hom_inv_id
  inv_hom_id := by
    calc
      Hom.comp (Hom.comp e'.inv e.inv) (Hom.comp e.hom e'.hom) =
          Hom.comp e'.inv (Hom.comp e.inv (Hom.comp e.hom e'.hom)) :=
        Hom.assoc e'.inv e.inv (Hom.comp e.hom e'.hom)
      _ = Hom.comp e'.inv (Hom.comp (Hom.comp e.inv e.hom) e'.hom) := by
        rw [Hom.assoc e.inv e.hom e'.hom]
      _ = Hom.comp e'.inv e'.hom := by rw [e.inv_hom_id, Hom.id_comp]
      _ = Hom.id H := e'.inv_hom_id

end HomIso

/-- A cohomological delta functor is universal when every degree-zero natural
transformation out of it extends uniquely to a morphism of delta functors. -/
@[stacks 010S]
class IsUniversal (F : CohomologicalDeltaFunctor A B) : Prop where
  /-- The universal degree-zero extension property. -/
  existsUnique_hom (G : CohomologicalDeltaFunctor A B) (t : (F.F 0).obj ⟶ (G.F 0).obj) :
    ∃! τ : Hom F G, τ.app 0 = t

namespace IsUniversal

/-- A morphism out of a universal cohomological delta functor is determined by its
degree-zero component. -/
theorem hom_ext
    {F G : CohomologicalDeltaFunctor A B} [IsUniversal F]
    {τ σ : Hom F G} (h : τ.app 0 = σ.app 0) :
    τ = σ := sorry

/-- An isomorphism out of a universal cohomological delta functor is determined by its
degree-zero component. -/
theorem iso_ext
    {F G : CohomologicalDeltaFunctor A B} [IsUniversal F]
    {e e' : HomIso F G} (h : e.hom.app 0 = e'.hom.app 0) :
    e = e' := sorry

/-- Universal cohomological delta functors with a prescribed common degree-zero term are
uniquely isomorphic. -/
@[stacks 010U]
theorem uniqueIso
    {F : A ⥤ B}
    {G H : CohomologicalDeltaFunctor A B}
    [IsUniversal G] [IsUniversal H]
    (eG : (G.F 0).obj ≅ F) (eH : (H.F 0).obj ≅ F) :
    ∃! e : HomIso G H, e.hom.app 0 = eG.hom ≫ eH.inv := sorry

/-- Universal cohomological delta functors are uniquely isomorphic once their degree-zero
comparison is an isomorphism.  The `IsIso` proof is an ordinary argument so a client can use a
one-off certificate without introducing a local instance. -/
theorem uniqueIso_of_isIso
    {G H : CohomologicalDeltaFunctor A B}
    [IsUniversal G] [IsUniversal H]
    (t : (G.F 0).obj ⟶ (H.F 0).obj) (ht : IsIso t) :
    ∃! e : HomIso G H, e.hom.app 0 = t := sorry

end IsUniversal

end CohomologicalDeltaFunctor

end CategoryTheory
