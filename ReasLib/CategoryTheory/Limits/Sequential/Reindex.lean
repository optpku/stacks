/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Order.WellFounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing Sequential Diagrams

This leaf provides reindexing of a sequential diagram along a monotone self-map of `ℕ`.
An inflationary map induces a canonical natural transformation to the reindexed diagram;
fixed index maps act functorially on diagrams, with canonical identity and composition
comparisons. Strictly increasing maps give the commonly used subsequence specialization.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.SequentialDiagram

variable {C : Type u} [Category.{v} C]

/-- Reindex a sequential diagram along a monotone self-map of `ℕ`. -/
def reindex (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : Monotone s) : ℕ ⥤ C :=
  hs.functor ⋙ K

/-- Reindexing evaluates the original diagram at the reindexed stage. -/
@[simp]
theorem reindex_obj (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : Monotone s) (n : ℕ) :
    (reindex K hs).obj n = K.obj (s n) := sorry

/-- Reindexing maps an order morphism by applying the original diagram to its monotone image. -/
@[simp]
theorem reindex_map (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : Monotone s)
    {m n : ℕ} (f : m ⟶ n) :
    (reindex K hs).map f = K.map (homOfLE (hs f.le)) := sorry

/-- Reindex a morphism of sequential diagrams along a fixed monotone self-map of `ℕ`. -/
def reindexMap {K L : ℕ ⥤ C} {s : ℕ → ℕ} (hs : Monotone s) (f : K ⟶ L) :
    reindex K hs ⟶ reindex L hs :=
  Functor.whiskerLeft hs.functor f

/-- Reindexing a diagram morphism evaluates its component at the reindexed stage. -/
@[simp]
theorem reindexMap_app {K L : ℕ ⥤ C} {s : ℕ → ℕ} (hs : Monotone s)
    (f : K ⟶ L) (n : ℕ) :
    (reindexMap hs f).app n = f.app (s n) := sorry

/-- Reindexing preserves identity morphisms of sequential diagrams. -/
@[simp]
theorem reindexMap_id (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : Monotone s) :
    reindexMap hs (𝟙 K) = 𝟙 (reindex K hs) := sorry

/-- Reindexing preserves composition of morphisms of sequential diagrams. -/
@[simp]
theorem reindexMap_comp {K L M : ℕ ⥤ C} {s : ℕ → ℕ} (hs : Monotone s)
    (f : K ⟶ L) (g : L ⟶ M) :
    reindexMap hs (f ≫ g) = reindexMap hs f ≫ reindexMap hs g := sorry

/-- Reindexing along a fixed monotone self-map is an endofunctor on sequential diagrams. -/
def reindexFunctor {s : ℕ → ℕ} (hs : Monotone s) : (ℕ ⥤ C) ⥤ (ℕ ⥤ C) :=
  (Functor.whiskeringLeft ℕ ℕ C).obj hs.functor

/-- The object action of the fixed reindexing functor is `reindex`. -/
@[simp]
theorem reindexFunctor_obj (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : Monotone s) :
    (reindexFunctor hs).obj K = reindex K hs := sorry

/-- The morphism action of the fixed reindexing functor is `reindexMap`. -/
@[simp]
theorem reindexFunctor_map {K L : ℕ ⥤ C} {s : ℕ → ℕ} (hs : Monotone s)
    (f : K ⟶ L) :
    (reindexFunctor hs).map f = reindexMap hs f := sorry

/-- The component formula for the morphism action of the fixed reindexing functor. -/
@[simp]
theorem reindexFunctor_map_app {K L : ℕ ⥤ C} {s : ℕ → ℕ} (hs : Monotone s)
    (f : K ⟶ L) (n : ℕ) :
    ((reindexFunctor hs).map f).app n = f.app (s n) := sorry

namespace Index

/-- The functor induced by the identity monotone map is naturally isomorphic to the identity
functor on the preorder category `ℕ`. -/
def idIso :
    (monotone_id : Monotone (id : ℕ → ℕ)).functor ≅ 𝟭 ℕ :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

/-- The functor induced by a composite of monotone maps is naturally isomorphic to the
composite of their induced functors. -/
def compIso {s t : ℕ → ℕ} (hs : Monotone s) (ht : Monotone t) :
    (ht.comp hs).functor ≅ hs.functor ⋙ ht.functor :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

end Index

/-- Reindexing along the identity map is naturally isomorphic to the identity endofunctor on
sequential diagrams. -/
def reindexFunctorIdIso :
    reindexFunctor (C := C) (monotone_id : Monotone (id : ℕ → ℕ)) ≅ 𝟭 (ℕ ⥤ C) :=
  (Functor.whiskeringLeft ℕ ℕ C).mapIso Index.idIso ≪≫
    Functor.whiskeringLeftObjIdIso

/-- Reindexing along a composite is naturally isomorphic to applying the two reindexing
endofunctors successively. -/
def reindexFunctorCompIso {s t : ℕ → ℕ} (hs : Monotone s) (ht : Monotone t) :
    reindexFunctor (C := C) (ht.comp hs) ≅
      reindexFunctor (C := C) ht ⋙ reindexFunctor (C := C) hs :=
  (Functor.whiskeringLeft ℕ ℕ C).mapIso (Index.compIso hs ht) ≪≫
    Functor.whiskeringLeftObjCompIso hs.functor ht.functor

/-- A sequential diagram reindexed by the identity map is canonically isomorphic to the
original diagram. -/
def reindexIdIso (K : ℕ ⥤ C) :
    reindex K (monotone_id : Monotone (id : ℕ → ℕ)) ≅ K :=
  reindexFunctorIdIso.app K

/-- Reindexing a sequential diagram along a composite agrees, up to canonical isomorphism,
with successive reindexing. -/
def reindexCompIso (K : ℕ ⥤ C) {s t : ℕ → ℕ} (hs : Monotone s) (ht : Monotone t) :
    reindex K (ht.comp hs) ≅ reindex (reindex K ht) hs :=
  (reindexFunctorCompIso hs ht).app K

namespace reindexFunctorIdIso

/-- The component of the identity comparison of reindexing functors is `reindexIdIso`. -/
@[simp]
theorem app (K : ℕ ⥤ C) :
    reindexFunctorIdIso.app K = reindexIdIso K := sorry

end reindexFunctorIdIso

namespace reindexIdIso

/-- The forward identity-reindexing comparison is pointwise the identity. -/
@[simp]
theorem hom_app (K : ℕ ⥤ C) (n : ℕ) :
    (reindexIdIso K).hom.app n = 𝟙 (K.obj n) := sorry

/-- The inverse identity-reindexing comparison is pointwise the identity. -/
@[simp]
theorem inv_app (K : ℕ ⥤ C) (n : ℕ) :
    (reindexIdIso K).inv.app n = 𝟙 (K.obj n) := sorry

end reindexIdIso

namespace reindexFunctorCompIso

/-- The component of the composite comparison of reindexing functors is `reindexCompIso`. -/
@[simp]
theorem app (K : ℕ ⥤ C) {s t : ℕ → ℕ} (hs : Monotone s) (ht : Monotone t) :
    (reindexFunctorCompIso hs ht).app K = reindexCompIso K hs ht := sorry

end reindexFunctorCompIso

namespace reindexCompIso

/-- The forward composite-reindexing comparison is pointwise the identity. -/
@[simp]
theorem hom_app (K : ℕ ⥤ C) {s t : ℕ → ℕ} (hs : Monotone s) (ht : Monotone t)
    (n : ℕ) :
    (reindexCompIso K hs ht).hom.app n = 𝟙 (K.obj (t (s n))) := sorry

/-- The inverse composite-reindexing comparison is pointwise the identity. -/
@[simp]
theorem inv_app (K : ℕ ⥤ C) {s t : ℕ → ℕ} (hs : Monotone s) (ht : Monotone t)
    (n : ℕ) :
    (reindexCompIso K hs ht).inv.app n = 𝟙 (K.obj (t (s n))) := sorry

end reindexCompIso

/-- Naturality of the component maps from a sequential diagram to an inflationary monotone
reindexing. -/
theorem toReindex_naturality (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : Monotone s)
    (hle : ∀ n : ℕ, n ≤ s n) {m n : ℕ} (f : m ⟶ n) :
    K.map f ≫ K.map (homOfLE (hle n)) =
      K.map (homOfLE (hle m)) ≫ (reindex K hs).map f := sorry

/-- The natural transformation from a sequential diagram to an inflationary monotone
reindexing, with component `K.map (homOfLE (hle n))` at stage `n`. -/
def toReindex (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : Monotone s)
    (hle : ∀ n : ℕ, n ≤ s n) : K ⟶ reindex K hs where
  app n := K.map (homOfLE (hle n))
  naturality := fun _ _ f ↦ toReindex_naturality K hs hle f

/-- The component of the canonical map to an inflationary reindexing is the corresponding
structure map of the original diagram. -/
@[simp]
theorem toReindex_app (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : Monotone s)
    (hle : ∀ n : ℕ, n ≤ s n) (n : ℕ) :
    (toReindex K hs hle).app n = K.map (homOfLE (hle n)) := sorry

/-- The canonical map to an inflationary reindexing is natural in the sequential diagram. -/
@[reassoc]
theorem toReindex_map {K L : ℕ ⥤ C} {s : ℕ → ℕ} (hs : Monotone s)
    (hle : ∀ n : ℕ, n ≤ s n) (f : K ⟶ L) :
    f ≫ toReindex L hs hle = toReindex K hs hle ≫ reindexMap hs f := sorry

/-- For an inflationary monotone map, the canonical maps to reindexed diagrams assemble into
a natural transformation of endofunctors. -/
def toReindexNatTrans {s : ℕ → ℕ} (hs : Monotone s) (hle : ∀ n : ℕ, n ≤ s n) :
    𝟭 (ℕ ⥤ C) ⟶ reindexFunctor hs where
  app K := toReindex K hs hle
  naturality := fun _ _ f ↦ toReindex_map hs hle f

namespace toReindexNatTrans

/-- Evaluating the natural transformation to an inflationary reindexing at a diagram gives
`toReindex`. -/
@[simp]
theorem app (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : Monotone s) (hle : ∀ n : ℕ, n ≤ s n) :
    (toReindexNatTrans hs hle).app K = toReindex K hs hle := sorry

/-- The stage component of the natural transformation to an inflationary reindexing is the
corresponding structure map. -/
@[simp]
theorem app_app (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : Monotone s)
    (hle : ∀ n : ℕ, n ≤ s n) (n : ℕ) :
    ((toReindexNatTrans hs hle).app K).app n = K.map (homOfLE (hle n)) := sorry

end toReindexNatTrans

/-- The subsequence of a sequential diagram selected by a strictly increasing map. -/
@[stacks 0CRJ "strictly increasing subsequence diagram"]
def subsequence (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : StrictMono s) : ℕ ⥤ C :=
  reindex K hs.monotone

/-- The `n`th object of a subsequence diagram is the object at stage `s n` of the full diagram. -/
@[simp]
theorem subsequence_obj (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ) :
    (subsequence K hs).obj n = K.obj (s n) := sorry

/-- A subsequence diagram maps an order morphism through the monotone index map. -/
@[simp]
theorem subsequence_map (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : StrictMono s)
    {m n : ℕ} (f : m ⟶ n) :
    (subsequence K hs).map f = K.map (homOfLE (hs.monotone f.le)) := sorry

/-- Reindex a morphism of sequential diagrams along a strictly increasing subsequence. -/
def subsequenceMap {K L : ℕ ⥤ C} {s : ℕ → ℕ} (hs : StrictMono s) (f : K ⟶ L) :
    subsequence K hs ⟶ subsequence L hs :=
  reindexMap hs.monotone f

/-- A reindexed diagram morphism has at stage `n` the component at stage `s n`. -/
@[simp]
theorem subsequenceMap_app {K L : ℕ ⥤ C} {s : ℕ → ℕ} (hs : StrictMono s)
    (f : K ⟶ L) (n : ℕ) :
    (subsequenceMap hs f).app n = f.app (s n) := sorry

/-- Subsequence reindexing preserves identity morphisms. -/
@[simp]
theorem subsequenceMap_id (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : StrictMono s) :
    subsequenceMap hs (𝟙 K) = 𝟙 (subsequence K hs) := sorry

/-- Subsequence reindexing preserves composition of diagram morphisms. -/
@[simp]
theorem subsequenceMap_comp {K L M : ℕ ⥤ C} {s : ℕ → ℕ} (hs : StrictMono s)
    (f : K ⟶ L) (g : L ⟶ M) :
    subsequenceMap hs (f ≫ g) = subsequenceMap hs f ≫ subsequenceMap hs g := sorry

/-- A fixed strictly increasing subsequence defines an endofunctor on sequential diagrams. -/
@[stacks 0CRJ "functorial strictly increasing subsequence reindexing"]
def subsequenceFunctor {s : ℕ → ℕ} (hs : StrictMono s) : (ℕ ⥤ C) ⥤ (ℕ ⥤ C) :=
  reindexFunctor hs.monotone

/-- The object action of the fixed subsequence functor is `subsequence`. -/
@[simp]
theorem subsequenceFunctor_obj (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : StrictMono s) :
    (subsequenceFunctor hs).obj K = subsequence K hs := sorry

/-- The morphism action of the fixed subsequence functor is `subsequenceMap`. -/
@[simp]
theorem subsequenceFunctor_map {K L : ℕ ⥤ C} {s : ℕ → ℕ} (hs : StrictMono s)
    (f : K ⟶ L) :
    (subsequenceFunctor hs).map f = subsequenceMap hs f := sorry

/-- The component formula for the morphism action of the fixed subsequence functor. -/
@[simp]
theorem subsequenceFunctor_map_app {K L : ℕ ⥤ C} {s : ℕ → ℕ}
    (hs : StrictMono s) (f : K ⟶ L) (n : ℕ) :
    ((subsequenceFunctor hs).map f).app n = f.app (s n) := sorry

/-- The canonical natural transformation from a sequential diagram to a strictly increasing
subsequence. -/
@[stacks 0CRJ "map from a sequential diagram to a subsequence"]
def toSubsequence (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : StrictMono s) :
    K ⟶ subsequence K hs :=
  toReindex K hs.monotone fun n ↦ hs.le_apply (x := n)

/-- At stage `n`, the canonical map to a subsequence is the structure map from `n` to `s n`. -/
@[simp]
theorem toSubsequence_app (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ) :
    (toSubsequence K hs).app n =
      K.map (homOfLE (hs.le_apply (x := n))) := sorry

/-- The canonical map to a strictly increasing subsequence is natural in the sequential
diagram. -/
@[reassoc]
theorem toSubsequence_map {K L : ℕ ⥤ C} {s : ℕ → ℕ} (hs : StrictMono s)
    (f : K ⟶ L) :
    f ≫ toSubsequence L hs = toSubsequence K hs ≫ subsequenceMap hs f := sorry

/-- The canonical maps to a fixed strictly increasing subsequence form a natural
transformation of endofunctors. -/
@[stacks 0CRJ "naturality of maps to a strictly increasing subsequence"]
def toSubsequenceNatTrans {s : ℕ → ℕ} (hs : StrictMono s) :
    𝟭 (ℕ ⥤ C) ⟶ subsequenceFunctor hs :=
  toReindexNatTrans hs.monotone fun n ↦ hs.le_apply (x := n)

namespace toSubsequenceNatTrans

/-- Evaluating the natural transformation to a fixed subsequence gives `toSubsequence`. -/
@[simp]
theorem app (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : StrictMono s) :
    (toSubsequenceNatTrans hs).app K = toSubsequence K hs := sorry

/-- The stage component of the natural transformation to a subsequence is the corresponding
structure map. -/
@[simp]
theorem app_app (K : ℕ ⥤ C) {s : ℕ → ℕ} (hs : StrictMono s) (n : ℕ) :
    ((toSubsequenceNatTrans hs).app K).app n =
      K.map (homOfLE (hs.le_apply (x := n))) := sorry

end toSubsequenceNatTrans

end CategoryTheory.SequentialDiagram
