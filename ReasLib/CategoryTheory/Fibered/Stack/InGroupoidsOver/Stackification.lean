/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Existence
public import ReasLib.CategoryTheory.Fibered.Groupoids.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Precomposition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence and uniqueness of stackifications in groupoids

This leaf owns the groupoid-valued existence specialization and the fixed-universe bundled
uniqueness theorem. Heterogeneous universal properties are inherited directly from the shared
`CartesianBasedFunctor.IsStackification` owner.
-/

@[expose] public section

universe u v uX vX w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
namespace Functor.IsFibered.InGroupoids.Stackification

/-- Every groupoid-fibred projection over a site admits a stackification in groupoids in a
sufficiently large universe, with a heterogeneous cartesian comparison. -/
@[stacks 02ZP "universe-polymorphic stackification in groupoids"]
theorem existsOverSite
    (J : GrothendieckTopology C)
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C)
    [Functor.IsFibered.InGroupoids p] :
    ∃ Y : StackOver.Groupoids.{
        u, v, max u (max v (max uX vX)), max v vX} J,
      ∃ G : CartesianBasedFunctor p Y.p,
        CartesianBasedFunctor.IsStackification J G := sorry

/-- An explicit groupoid-valued stackification presentation.

This is the groupoid refinement of the neutral
`Functor.IsFibered.Stackification.Presentation` owner.  The target is kept in
`StackOver.Groupoids` so downstream groupoid arguments do not have to recover the fiber-shape
condition from an existential witness.  The comparison and its predicate are still the shared
`CartesianBasedFunctor` owners; this structure does not define a second stackification notion. -/
@[stacks 02ZP "explicit stackification presentation in groupoids"]
structure Presentation
    (J : GrothendieckTopology C)
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C)
    [Functor.IsFibered.InGroupoids p] where
  /-- The target stack in groupoids. -/
  target : StackOver.Groupoids.{
      u, v, max u (max v (max uX vX)), max v vX} J
  /-- The cartesian comparison from the original groupoid-fibred category. -/
  comparison : CartesianBasedFunctor p target.p
  /-- The comparison satisfies the shared stackification predicate. -/
  isStackification : CartesianBasedFunctor.IsStackification J comparison

attribute [stacks 02ZP "groupoid stackification presentation target"] Presentation.target
attribute [stacks 02ZP "groupoid stackification presentation comparison"] Presentation.comparison
attribute [stacks 02ZP "groupoid stackification presentation predicate"]
  Presentation.isStackification

/-- Package explicitly supplied groupoid stackification presentation data. -/
@[stacks 02ZP "package explicit groupoid stackification presentation"]
def Presentation.of
    (J : GrothendieckTopology C)
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C)
    [Functor.IsFibered.InGroupoids p]
    (Y : StackOver.Groupoids.{
      u, v, max u (max v (max uX vX)), max v vX} J)
    (G : CartesianBasedFunctor p Y.p)
    (hG : CartesianBasedFunctor.IsStackification J G) :
    Presentation J p :=
  ⟨Y, G, hG⟩

/-- Convert the proposition-level groupoid existence theorem into the named presentation owner. -/
@[stacks 02ZP "package an existential groupoid stackification presentation"]
noncomputable def Presentation.ofExists
    (J : GrothendieckTopology C)
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C)
    [Functor.IsFibered.InGroupoids p]
    (h : ∃ Y : StackOver.Groupoids.{
        u, v, max u (max v (max uX vX)), max v vX} J,
      ∃ G : CartesianBasedFunctor p Y.p,
        CartesianBasedFunctor.IsStackification J G) :
    Presentation J p where
  target := Classical.choose h
  comparison := Classical.choose (Classical.choose_spec h)
  isStackification := Classical.choose_spec (Classical.choose_spec h)

/-- Every groupoid-fibred category has a nonempty type of groupoid stackification presentations. -/
@[stacks 02ZP "existence of groupoid stackification presentation data"]
theorem Presentation.nonempty
    (J : GrothendieckTopology C)
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C)
    [Functor.IsFibered.InGroupoids p] :
    Nonempty (Presentation J p) := sorry

/-- A convenient selected groupoid-valued stackification presentation. -/
@[stacks 02ZP "selected groupoid stackification presentation"]
noncomputable def presentation
    (J : GrothendieckTopology C)
    {S : Type uX} [Category.{vX} S] (p : S ⥤ C)
    [Functor.IsFibered.InGroupoids p] :
    Presentation J p :=
  Presentation.ofExists J p (existsOverSite J p)

/-- Forget the groupoid refinement and reuse the neutral stackification presentation owner. -/
@[stacks 02ZP "groupoid stackification presentation to neutral presentation"]
def Presentation.toPresentation
    {S : Type uX} [Category.{vX} S] {p : S ⥤ C}
    [Functor.IsFibered.InGroupoids p] (P : Presentation J p) :
    Functor.IsFibered.Stackification.Presentation J p :=
  ⟨P.target.toStackOver, P.comparison, P.isStackification⟩

/- Data audit: `Presentation` and `Presentation.of` carry only explicitly supplied groupoid target
and comparison data.  `ofExists` and `presentation` are the named proposition-to-data boundary;
their proof debt is confined to the Prop-valued stackification field. -/

end Functor.IsFibered.InGroupoids.Stackification

namespace StackOver.Groupoids.Stackification

variable {J : GrothendieckTopology C}

/-- The uniqueness clause of Lemma 8.9.1 (tag 02ZP): two stackification presentations in
groupoids admit a bicategorical equivalence, and every compatible comparison is uniquely
`2`-isomorphic to the chosen one. -/
@[stacks 02ZP "uniqueness of stackification in groupoids"]
theorem comparisonUnique
    {X : FiberedCategoryOver.Groupoids.{u, v, max u (max v uX), max v vX} C}
    {Y₁ Y₂ : StackOver.Groupoids.{u, v, max u (max v uX), max v vX} J}
    (G₁ : X ⟶ Y₁.toGroupoids) (G₂ : X ⟶ Y₂.toGroupoids)
    (hG₁ : FiberedCategoryOver.Groupoids.Hom.IsStackification J G₁)
    (hG₂ : FiberedCategoryOver.Groupoids.Hom.IsStackification J G₂) :
    ∃ e : Y₁ ≌ Y₂,
      ∃ α : (StackOver.Groupoids.Hom.precomp Y₂ G₁).obj e.hom ≅ G₂,
        ∀ (H : Y₁ ⟶ Y₂)
            (α' : (StackOver.Groupoids.Hom.precomp Y₂ G₁).obj H ≅ G₂),
          ∃! β : e.hom ≅ H,
            (StackOver.Groupoids.Hom.precomp Y₂ G₁).mapIso β ≪≫ α' = α := sorry

end StackOver.Groupoids.Stackification

end CategoryTheory
