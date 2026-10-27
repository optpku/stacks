/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.KInjective

/-!
# Functoriality of filtered K-injective resolutions

A map of resolutions remembers the comparison with the original filtered-complex map.  This is
the reusable input needed by any functorial construction on filtered K-injective models.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.FilteredComplex.KInjectiveResolution

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A morphism between filtered K-injective resolutions lying over a fixed morphism of the
original filtered complexes. -/
@[stacks 0BKI "morphism of filtered K-injective resolutions"]
structure Map {K L : FilteredComplex A} (f : K ⟶ L)
    (R : KInjectiveResolution K) (S : KInjectiveResolution L) where
  /-- The morphism between the resolving filtered complexes. -/
  hom : R.complex ⟶ S.complex
  /-- Compatibility with the two resolution morphisms. -/
  ι_naturality : R.ι ≫ hom = f ≫ S.ι

namespace Map

/-- Maps of filtered K-injective resolutions are determined by their morphism between the
resolving complexes. -/
@[ext, stacks 0BKI "extensionality of maps of filtered K-injective resolutions"]
theorem ext {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {m n : Map f R S} (h : m.hom = n.hom) : m = n := by
  cases m
  cases n
  cases h
  rfl

/-- The identity morphism satisfies the resolution comparison square. -/
@[stacks 0BKI "identity map of a filtered K-injective resolution"]
theorem idNaturality {K : FilteredComplex A} (R : KInjectiveResolution K) :
    R.ι ≫ 𝟙 R.complex = (𝟙 K) ≫ R.ι := by
  simp

/-- The identity morphism of a filtered K-injective resolution. -/
@[stacks 0BKI "identity map of a filtered K-injective resolution"]
def id {K : FilteredComplex A} (R : KInjectiveResolution K) : Map (𝟙 K) R R where
  hom := 𝟙 R.complex
  ι_naturality := idNaturality R

/-- The morphism between resolving complexes underlying the identity resolution map is the
identity. -/
@[simp, stacks 0BKI "identity map of a filtered K-injective resolution"]
theorem id_hom {K : FilteredComplex A} (R : KInjectiveResolution K) :
    (id R).hom = 𝟙 R.complex := rfl

/-- The composite morphism satisfies the comparison square for the composite source map. -/
@[stacks 0BKI "composition of maps of filtered K-injective resolutions"]
theorem compNaturality {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {T : KInjectiveResolution M} (m : Map f R S) (n : Map g S T) :
    R.ι ≫ (m.hom ≫ n.hom) = (f ≫ g) ≫ T.ι := by
  rw [← Category.assoc, m.ι_naturality, Category.assoc, n.ι_naturality,
    Category.assoc]

/-- The composite of maps of filtered K-injective resolutions. -/
@[stacks 0BKI "composition of maps of filtered K-injective resolutions"]
def comp {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {T : KInjectiveResolution M} (m : Map f R S) (n : Map g S T) :
    Map (f ≫ g) R T where
  hom := m.hom ≫ n.hom
  ι_naturality := compNaturality m n

/-- The morphism between resolving complexes underlying a composite resolution map is the
composite morphism. -/
@[simp, stacks 0BKI "composition of maps of filtered K-injective resolutions"]
theorem comp_hom {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {T : KInjectiveResolution M} (m : Map f R S) (n : Map g S T) :
    (comp m n).hom = m.hom ≫ n.hom := rfl

/-- Reindexing a resolution map along an equality of source morphisms preserves its comparison
square. -/
@[stacks 0BKI "reindexing a map of filtered K-injective resolutions"]
theorem reindexNaturality {K L : FilteredComplex A} {f g : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    (h : f = g) (m : Map f R S) : R.ι ≫ m.hom = g ≫ S.ι := by
  rw [← h]
  exact m.ι_naturality

/-- Reindex a map of filtered K-injective resolutions along an equality of source morphisms,
without changing its morphism between resolving complexes. -/
@[stacks 0BKI "reindexing a map of filtered K-injective resolutions"]
def reindex {K L : FilteredComplex A} {f g : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    (h : f = g) (m : Map f R S) : Map g R S where
  hom := m.hom
  ι_naturality := reindexNaturality h m

/-- Reindexing a resolution map does not change its morphism between resolving complexes. -/
@[simp, stacks 0BKI "reindexing a map of filtered K-injective resolutions"]
theorem reindex_hom {K L : FilteredComplex A} {f g : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    (h : f = g) (m : Map f R S) : (reindex h m).hom = m.hom := rfl

/-- Reindexing along reflexivity leaves a resolution map unchanged. -/
@[simp, stacks 0BKI "reindexing a map of filtered K-injective resolutions"]
theorem reindex_rfl {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L} (m : Map f R S) :
    reindex rfl m = m := by
  apply ext
  rfl

/-- Successive reindexings of a filtered K-injective resolution map combine by transitivity. -/
@[simp, stacks 0BKI "transitivity of filtered K-injective map transport"]
theorem reindex_trans {K L : FilteredComplex A} {f f' f'' : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    (e : f = f') (e' : f' = f'') (m : Map f R S) :
    reindex e' (reindex e m) = reindex (e.trans e') m := by
  apply ext
  rfl

/-- Reindexing along an equality and its inverse recovers a filtered K-injective resolution map. -/
@[simp, stacks 0BKI "inverse filtered K-injective map transport"]
theorem reindex_symm {K L : FilteredComplex A} {f f' : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    (e : f = f') (m : Map f R S) :
    reindex e.symm (reindex e m) = m := by
  apply ext
  rfl

/-- Reindexing the left factor of a composite filtered K-injective map commutes with composition. -/
@[simp, stacks 0BKI "left-factor filtered K-injective map transport"]
theorem reindex_comp_left {K L M : FilteredComplex A} {f f' : K ⟶ L} {g : L ⟶ M}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {T : KInjectiveResolution M} (e : f = f') (m : Map f R S) (n : Map g S T) :
    reindex (congrArg (fun k : K ⟶ L => k ≫ g) e) (comp m n) =
      comp (reindex e m) n := by
  apply ext
  rfl

/-- Reindexing the right factor of a composite filtered K-injective map commutes with composition. -/
@[simp, stacks 0BKI "right-factor filtered K-injective map transport"]
theorem reindex_comp_right {K L M : FilteredComplex A} {f : K ⟶ L} {g g' : L ⟶ M}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {T : KInjectiveResolution M} (e : g = g') (m : Map f R S) (n : Map g S T) :
    reindex (congrArg (fun k : L ⟶ M => f ≫ k) e) (comp m n) =
      comp m (reindex e n) := by
  apply ext
  rfl

/-- Reindexing both factors of a composite filtered K-injective map commutes with composition. -/
@[simp, stacks 0BKI "two-factor filtered K-injective map transport"]
theorem reindex_comp {K L M : FilteredComplex A} {f f' : K ⟶ L} {g g' : L ⟶ M}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {T : KInjectiveResolution M} (e : f = f') (e' : g = g')
    (m : Map f R S) (n : Map g S T) :
    reindex (congrArg₂ (fun (a : K ⟶ L) (b : L ⟶ M) => a ≫ b) e e') (comp m n) =
      comp (reindex e m) (reindex e' n) := by
  apply ext
  rfl

/-- The identity resolution map is a left identity after reindexing the source morphism. -/
@[stacks 0BKI "left identity for maps of filtered K-injective resolutions"]
theorem id_comp {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L} (m : Map f R S) :
    reindex (Category.id_comp f) (comp (id R) m) = m := by
  apply ext
  exact Category.id_comp m.hom

/-- The identity resolution map is a right identity after reindexing the source morphism. -/
@[stacks 0BKI "right identity for maps of filtered K-injective resolutions"]
theorem comp_id {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L} (m : Map f R S) :
    reindex (Category.comp_id f) (comp m (id S)) = m := by
  apply ext
  exact Category.comp_id m.hom

/-- Composition of resolution maps is associative after reindexing the source morphism. -/
@[stacks 0BKI "associativity of maps of filtered K-injective resolutions"]
theorem assoc {K L M N : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {h : M ⟶ N} {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {T : KInjectiveResolution M} {U : KInjectiveResolution N}
    (m : Map f R S) (n : Map g S T) (k : Map h T U) :
    reindex (Category.assoc f g h) (comp (comp m n) k) = comp m (comp n k) := by
  apply ext
  exact Category.assoc m.hom n.hom k.hom

end Map

/-- A filtered-complex morphism admits compatible choices of filtered K-injective resolutions. -/
@[stacks 0BKI "functoriality"]
theorem existsMap [IsGrothendieckAbelian.{w} A]
    {K L : FilteredComplex A} (f : K ⟶ L) :
    ∃ (R : KInjectiveResolution K) (S : KInjectiveResolution L), Nonempty (Map f R S) := sorry

end CategoryTheory.FilteredComplex.KInjectiveResolution
