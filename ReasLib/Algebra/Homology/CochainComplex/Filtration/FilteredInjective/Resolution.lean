/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.StrictReplacement
public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict Filtered-Injective Resolutions

This leaf specializes the property-neutral strict replacement datum to finite filtered objects.
It owns both the replacement of a degree-zero complex and the compatible lifting of morphisms
between such replacements.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredInjectivePlus

/-- A bounded-below, termwise monomorphic strict filtered-injective replacement whose associated
graded comparison is a quasi-isomorphism. -/
@[stacks 05TT "strict filtered-injective replacement"]
abbrev IsStrictReplacement
    (a : ℤ) {K : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (I : FilteredInjectivePlus C)
    (f : K ⟶ (FilteredInjectivePlus.ι C).obj I) : Prop :=
  _root_.CochainComplex.FilteredReplacement.IsStrict
    (FilteredObject.Finite.inclusion C)
    (FilteredObject.Finite.AssociatedGraded.functor C)
    (FilteredObject.Finite.FilteredInjective.property C) a I f

/-- A chosen strict filtered-injective resolution of a bounded-below complex of finite filtered
objects.  The lower bound belongs to the chosen resolution; downstream constructions only need
the bundled bounded-below source. -/
@[stacks 05TW "strict filtered-injective resolution"]
structure Resolution (K : CochainComplex.Plus (FilteredObject.Finite.category C)) where
  /-- A lower bound respected by the chosen resolving complex. -/
  lowerBound : ℤ
  /-- The bounded-below termwise filtered-injective resolving complex. -/
  complex : FilteredInjectivePlus C
  /-- The comparison from the original complex to the resolving complex. -/
  ι : K.obj ⟶ (FilteredInjectivePlus.ι C).obj complex
  /-- The comparison is termwise monomorphic and strict, and is a filtered quasi-isomorphism. -/
  isStrict : IsStrictReplacement lowerBound complex ι

namespace Resolution

/-- The resolving complex vanishes strictly below its chosen lower bound. -/
@[stacks 05TW "strict filtered-injective resolution"]
theorem strictlyGE {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) :
    ((FilteredInjectivePlus.ι C).obj R.complex).IsStrictlyGE R.lowerBound := sorry

/-- The comparison of a strict filtered-injective resolution is monomorphic in every degree. -/
@[stacks 05TW "strict filtered-injective resolution"]
theorem termMono {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) (n : ℤ) : Mono (R.ι.f n) := sorry

/-- The comparison of a strict filtered-injective resolution is a filtered
quasi-isomorphism. -/
@[stacks 05TW "strict filtered-injective resolution"]
theorem quasiIso {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) :
    FilteredObject.Finite.CochainComplex.quasiIso C R.ι := sorry

/-- Every component of a strict filtered-injective resolution comparison is strict. -/
@[stacks 05TW "strict filtered-injective resolution"]
theorem termStrict {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) (n : ℤ) :
    FilteredObject.Hom.Strict ((FilteredObject.Finite.inclusion C).map (R.ι.f n)) := sorry

/-- Every bounded-below complex of finite filtered objects admits a strict filtered-injective
resolution. -/
@[stacks 05TW "existence of strict filtered-injective resolutions"]
theorem nonempty [EnoughInjectives C]
    (K : CochainComplex.Plus (FilteredObject.Finite.category C)) :
    Nonempty (Resolution K) := sorry

/-- A morphism between chosen strict filtered-injective resolutions lying over a fixed morphism
of their bounded-below source complexes. -/
@[stacks 05TU "morphism of strict filtered-injective resolutions"]
structure Map {K L : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (f : K ⟶ L) (R : Resolution K) (S : Resolution L) where
  /-- The morphism between the resolving complexes. -/
  hom : (FilteredInjectivePlus.ι C).obj R.complex ⟶
    (FilteredInjectivePlus.ι C).obj S.complex
  /-- Compatibility with the two resolution comparisons. -/
  ι_naturality : R.ι ≫ hom = f.hom ≫ S.ι

namespace Map

/-- Maps of strict filtered-injective resolutions are determined by their morphisms between the
resolving complexes. -/
@[ext, stacks 05TU "extensionality of maps of strict filtered-injective resolutions"]
theorem ext {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} {m n : Map f R S}
    (h : m.hom = n.hom) : m = n := sorry

/-- The identity morphism satisfies the comparison square for a strict filtered-injective
resolution. -/
@[stacks 05TU "identity map of a strict filtered-injective resolution"]
theorem idNaturality {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) :
    R.ι ≫ 𝟙 ((FilteredInjectivePlus.ι C).obj R.complex) =
      (𝟙 K : K ⟶ K).hom ≫ R.ι := sorry

/-- The identity morphism of a strict filtered-injective resolution. -/
@[stacks 05TU "identity map of a strict filtered-injective resolution"]
def id {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) : Map (𝟙 K) R R where
  hom := 𝟙 ((FilteredInjectivePlus.ι C).obj R.complex)
  ι_naturality := idNaturality R

/-- The morphism underlying the identity resolution map is the identity. -/
@[simp, stacks 05TU "identity map of a strict filtered-injective resolution"]
theorem id_hom {K : CochainComplex.Plus (FilteredObject.Finite.category C)}
    (R : Resolution K) :
    (id R).hom = 𝟙 ((FilteredInjectivePlus.ι C).obj R.complex) := sorry

/-- The composite morphism satisfies the comparison square for the composite source map. -/
@[stacks 05TU "composition of maps of strict filtered-injective resolutions"]
theorem compNaturality
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {T : Resolution M} (m : Map f R S) (n : Map g S T) :
    R.ι ≫ (m.hom ≫ n.hom) = (f ≫ g).hom ≫ T.ι := sorry

/-- The composite of maps of strict filtered-injective resolutions. -/
@[stacks 05TU "composition of maps of strict filtered-injective resolutions"]
def comp {K L M : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {T : Resolution M} (m : Map f R S) (n : Map g S T) : Map (f ≫ g) R T where
  hom := m.hom ≫ n.hom
  ι_naturality := compNaturality m n

/-- The morphism underlying a composite resolution map is the composite morphism. -/
@[simp, stacks 05TU "composition of maps of strict filtered-injective resolutions"]
theorem comp_hom
    {K L M : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {R : Resolution K} {S : Resolution L}
    {T : Resolution M} (m : Map f R S) (n : Map g S T) :
    (comp m n).hom = m.hom ≫ n.hom := sorry

/-- Reindexing a resolution map along an equality of source morphisms preserves its comparison
square. -/
@[stacks 05TU "reindexing a map of strict filtered-injective resolutions"]
theorem reindexNaturality
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) :
    R.ι ≫ m.hom = g.hom ≫ S.ι := sorry

/-- Reindex a map of strict filtered-injective resolutions without changing the morphism between
resolving complexes. -/
@[stacks 05TU "reindexing a map of strict filtered-injective resolutions"]
def reindex {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) : Map g R S where
  hom := m.hom
  ι_naturality := reindexNaturality h m

/-- Reindexing does not change the morphism between resolving complexes. -/
@[simp, stacks 05TU "reindexing a map of strict filtered-injective resolutions"]
theorem reindex_hom
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f g : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (h : f = g) (m : Map f R S) :
    (reindex h m).hom = m.hom := sorry

/-- Reindexing along reflexivity leaves a resolution map unchanged. -/
@[simp, stacks 05TU "reindexing a map of strict filtered-injective resolutions"]
theorem reindex_rfl
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) :
    reindex rfl m = m := sorry

/-- The identity resolution map is a left identity after reindexing. -/
@[stacks 05TU "left identity for maps of strict filtered-injective resolutions"]
theorem id_comp
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) :
    reindex (Category.id_comp f) (comp (id R) m) = m := sorry

/-- The identity resolution map is a right identity after reindexing. -/
@[stacks 05TU "right identity for maps of strict filtered-injective resolutions"]
theorem comp_id
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} {f : K ⟶ L}
    {R : Resolution K} {S : Resolution L} (m : Map f R S) :
    reindex (Category.comp_id f) (comp m (id S)) = m := sorry

/-- Composition of resolution maps is associative after reindexing. -/
@[stacks 05TU "associativity of maps of strict filtered-injective resolutions"]
theorem assoc
    {K L M N : CochainComplex.Plus (FilteredObject.Finite.category C)}
    {f : K ⟶ L} {g : L ⟶ M} {h : M ⟶ N}
    {R : Resolution K} {S : Resolution L} {T : Resolution M} {U : Resolution N}
    (m : Map f R S) (n : Map g S T) (k : Map h T U) :
    reindex (Category.assoc f g h) (comp (comp m n) k) = comp m (comp n k) := sorry

/-- A morphism of bounded-below finite filtered complexes lifts between any two chosen strict
filtered-injective resolutions. -/
@[stacks 05TU "comparison map of strict filtered-injective resolutions"]
theorem nonempty
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L)
    (R : Resolution K) (S : Resolution L) : Nonempty (Map f R S) := sorry

end Map

/-- A morphism of bounded-below finite filtered complexes admits compatible choices of strict
filtered-injective resolutions. -/
@[stacks 05TU "functoriality of strict filtered-injective resolutions"]
theorem existsMap [EnoughInjectives C]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category C)} (f : K ⟶ L) :
    ∃ (R : Resolution K) (S : Resolution L), Nonempty (Map f R S) := sorry

end Resolution

/-- Every finite filtered object admits a degree-zero filtered quasi-isomorphism to a
filtered-injective complex that vanishes in negative degrees. -/
@[stacks 05TT "filtered-injective resolution"]
theorem exists_quasiIso_single [EnoughInjectives C]
    (A : FilteredObject.Finite.category C) :
    ∃ (I : FilteredInjectivePlus C)
      (f : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj A ⟶
        (FilteredInjectivePlus.ι C).obj I),
      ((FilteredInjectivePlus.ι C).obj I).IsStrictlyGE 0 ∧
        FilteredObject.Finite.CochainComplex.quasiIso C f := sorry

/-- Every finite filtered object has a degree-zero strict filtered-injective replacement. -/
@[stacks 05TT "strict filtered-injective replacement"]
theorem exists_strictReplacement_single [EnoughInjectives C]
    (A : FilteredObject.Finite.category C) :
    ∃ (I : FilteredInjectivePlus C)
      (f : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj A ⟶
        (FilteredInjectivePlus.ι C).obj I),
      IsStrictReplacement 0 I f := sorry

/-- A morphism of finite filtered objects lifts to a morphism between prescribed strict
filtered-injective replacements. -/
@[stacks 05TU "strict filtered-injective replacement"]
theorem exists_map_of_strictReplacements
    {A B : FilteredObject.Finite.category C} {I J : FilteredInjectivePlus C}
    (f : A ⟶ B)
    (a : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj A ⟶
      (FilteredInjectivePlus.ι C).obj I)
    (ha : IsStrictReplacement 0 I a)
    (b : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj B ⟶
      (FilteredInjectivePlus.ι C).obj J) :
    ∃ g : (FilteredInjectivePlus.ι C).obj I ⟶ (FilteredInjectivePlus.ι C).obj J,
      CommSq a
        ((CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).map f) g b := sorry

/-- A morphism of finite filtered objects lifts between degree-zero filtered quasi-isomorphisms
to bounded-below filtered-injective complexes. -/
@[stacks 05TU "filtered-injective comparison map"]
theorem exists_map_of_quasiIsos
    {A B : FilteredObject.Finite.category C} {I J : FilteredInjectivePlus C}
    (f : A ⟶ B)
    (a : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj A ⟶
      (FilteredInjectivePlus.ι C).obj I)
    (b : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj B ⟶
      (FilteredInjectivePlus.ι C).obj J)
    (hI : ((FilteredInjectivePlus.ι C).obj I).IsStrictlyGE 0)
    (hJ : ((FilteredInjectivePlus.ι C).obj J).IsStrictlyGE 0)
    (ha : FilteredObject.Finite.CochainComplex.quasiIso C a)
    (hb : FilteredObject.Finite.CochainComplex.quasiIso C b) :
    ∃ g : (FilteredInjectivePlus.ι C).obj I ⟶ (FilteredInjectivePlus.ι C).obj J,
      CommSq a
        ((CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).map f) g b := sorry

end FilteredInjectivePlus

end CochainComplex
