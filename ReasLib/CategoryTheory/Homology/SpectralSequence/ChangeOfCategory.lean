/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Changing the target category of a spectral sequence

An additive homology-preserving functor maps every page of a spectral sequence and transports the
successive-page homology isomorphisms.  The construction is functorial in spectral-sequence maps.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uC vC uD vD w

namespace CategoryTheory.SpectralSequence

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
variable {κ : Type w} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

/-- Map a spectral sequence through an additive functor that preserves homology. -/
@[stacks 011O "change of category for a spectral sequence"]
noncomputable def mapCategory (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (E : SpectralSequence C c r₀) : SpectralSequence D c r₀ where
  page r hr := (F.mapHomologicalComplex (c r)).obj (E.page r hr)
  iso r r' pq hrr' hr :=
    (E.page r hr).mapHomologyIso F pq ≪≫ F.mapIso (E.iso r r' pq hrr' hr)

/-- Map a morphism of spectral sequences through a homology-preserving additive functor. -/
@[stacks 011O "change of category for spectral-sequence maps"]
noncomputable def mapCategoryMap (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    {E E' : SpectralSequence C c r₀} (φ : E ⟶ E') :
    mapCategory F E ⟶ mapCategory F E' where
  hom r hr := (F.mapHomologicalComplex (c r)).map (φ.hom r hr)
  comm := sorry

/-- Changing the target category is functorial on the category of spectral sequences. -/
@[stacks 011O "change-of-category functor for spectral sequences"]
noncomputable def mapCategoryFunctor (F : C ⥤ D) [F.Additive] [F.PreservesHomology] :
    SpectralSequence C c r₀ ⥤ SpectralSequence D c r₀ where
  obj := mapCategory F
  map := mapCategoryMap F
  map_id := sorry
  map_comp := sorry

/-- The `r`-th page of a mapped spectral sequence is obtained by mapping the original page. -/
@[stacks 011O "pages after changing spectral-sequence category"]
theorem mapCategory_page (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r) :
    (mapCategory F E).page r hr = (F.mapHomologicalComplex (c r)).obj (E.page r hr) := sorry

/-- Every entry of a target-changed page is the image of the corresponding original entry. -/
@[simp, stacks 011O "page entries after changing spectral-sequence category"]
theorem mapCategory_page_X (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    ((mapCategory F E).page r hr).X pq = F.obj ((E.page r hr).X pq) := sorry

/-- Every differential of a target-changed page is the image of the original differential. -/
@[simp, stacks 011O "page differentials after changing spectral-sequence category"]
theorem mapCategory_page_d (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (E : SpectralSequence C c r₀) (r : ℤ) (hr : r₀ ≤ r) (pq pq' : κ) :
    ((mapCategory F E).page r hr).d pq pq' =
      F.map ((E.page r hr).d pq pq') := sorry

/-- The page map of a mapped spectral-sequence morphism is obtained by mapping the original page
map. -/
@[stacks 011O "maps after changing spectral-sequence category"]
theorem mapCategoryMap_hom (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    {E E' : SpectralSequence C c r₀} (φ : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) :
    (mapCategoryMap F φ).hom r hr =
      (F.mapHomologicalComplex (c r)).map (φ.hom r hr) := sorry

/- The following small computation and transport lemmas are the public interface for clients that
need to work componentwise.  They deliberately keep the homology-preservation assumptions on the
ambient functor and expose no implementation-specific proof fields. -/

/-- The entry component of a page map after changing the target category. -/
@[simp, stacks 011O "entry maps after changing spectral-sequence category"]
theorem mapCategoryMap_hom_f (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    {E E' : SpectralSequence C c r₀} (φ : E ⟶ E') (r : ℤ) (hr : r₀ ≤ r) (pq : κ) :
    ((mapCategoryMap F φ).hom r hr).f pq =
      F.map ((φ.hom r hr).f pq) := sorry

/-- The object part of the target-change functor is `mapCategory`. -/
@[simp, stacks 011O "object computation for target-change functor"]
theorem mapCategoryFunctor_obj (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (E : SpectralSequence C c r₀) :
    (mapCategoryFunctor F).obj E = mapCategory F E := sorry

/-- The morphism part of the target-change functor is `mapCategoryMap`. -/
@[simp, stacks 011O "map computation for target-change functor"]
theorem mapCategoryFunctor_map (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    {E E' : SpectralSequence C c r₀} (φ : E ⟶ E') :
    (mapCategoryFunctor F).map φ = mapCategoryMap F φ := sorry

/-- Changing the target category preserves identity spectral-sequence maps. -/
@[simp, stacks 011O "identity law for target-change maps"]
theorem mapCategoryMap_id (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (E : SpectralSequence C c r₀) :
    mapCategoryMap F (𝟙 E) = 𝟙 (mapCategory F E) := sorry

/-- Changing the target category preserves composition of spectral-sequence maps. -/
@[simp, stacks 011O "composition law for target-change maps"]
theorem mapCategoryMap_comp (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    {E E' E'' : SpectralSequence C c r₀} (φ : E ⟶ E') (ψ : E' ⟶ E'') :
    mapCategoryMap F (φ ≫ ψ) = mapCategoryMap F φ ≫ mapCategoryMap F ψ := sorry

/-- A categorical isomorphism is sent to an isomorphism of target-changed sequences. -/
@[stacks 011O "isomorphism transport under target change"]
theorem mapCategoryMap_isIso (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    {E E' : SpectralSequence C c r₀} (φ : E ⟶ E') [IsIso φ] :
    IsIso (mapCategoryMap F φ) := sorry

/-- An `IsIsoFrom` comparison is preserved by changing the target category. -/
@[stacks 011O "pagewise comparison transport under target change"]
theorem mapCategoryMap_isIsoFrom (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    {E E' : SpectralSequence C c r₀} (φ : E ⟶ E')
    {r : ℤ} (hr : r₀ ≤ r) (hφ : SpectralSequence.Hom.IsIsoFrom φ r hr) :
    SpectralSequence.Hom.IsIsoFrom (mapCategoryMap F φ) r hr := sorry

end CategoryTheory.SpectralSequence
