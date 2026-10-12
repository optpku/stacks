/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Over
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.PrecompLift
public import ReasLib.CategoryTheory.Fibered.CategoryOver.LocalEquivalence
public import ReasLib.CategoryTheory.Sites.Sheafification.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Stackification

A cartesian morphism of fibred categories is a stackification when its target is a stack and the
morphism is a local equivalence: its Hom-presheaf maps are local equivalences and every target
object is locally in its essential image.  This is the formal content of the two conditions in
Stacks Project, Lemma 8.8.1, and it implies the universal property against every stack.

## Main declarations

* `CategoryTheory.CartesianBasedFunctor.IsStackification` — the universe-polymorphic
  stackification predicate.
* `CategoryTheory.CartesianBasedFunctor.IsStackification.homSheafification` — the canonical
  Hom-presheaf sheafification presentation.
* `CategoryTheory.CartesianBasedFunctor.IsStackification.lift` — universal factorization.
* `CategoryTheory.CartesianBasedFunctor.IsStackification.precomp_isEquivalence` — the
  Hom-category universal property.
* `CategoryTheory.FiberedCategoryOver.Hom.IsStackification` — the fixed-universe specialization.
-/

@[expose] public section

universe u v w vS uS₁ vS₁ uS₂ vS₂ uS₃ vS₃

namespace CategoryTheory

open Functor Limits

variable {C : Type u} [Category.{v} C]

namespace CartesianBasedFunctor

variable {S₁ : Type uS₁} {S₂ : Type uS₂} [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C} [p₁.IsFibered] [p₂.IsFibered]

/-- A cartesian based functor is a stackification when it is a local equivalence and its target is
a stack.  Thus its Hom-presheaf maps exhibit sheafification after passage to the localizing class,
and its target objects are locally in the essential image. Source and target total categories may
live in independent universes. -/
@[stacks 02ZM "stackification of a fibred category",
  stacks 02ZN "stackification predicate"]
class IsStackification
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) : Prop where
  /-- The comparison is a local equivalence of fibred categories. -/
  isLocalEquivalence : IsLocalEquivalence J F
  /-- The target projection is a stack over the site. -/
  isStack : IsStack.OnSite J p₂

attribute [instance] IsStackification.isStack
attribute [stacks 02ZN "stackification local-equivalence field"]
  IsStackification.isLocalEquivalence
attribute [stacks 02ZN "stackification target-stack field"]
  IsStackification.isStack

/-- The local-equivalence and target-stack conditions are exactly the defining conditions of a
universe-polymorphic stackification. -/
@[stacks 02ZN "defining conditions of a fibred-category stackification"]
theorem IsStackification.iff_isLocalEquivalence_and_isStack
    (J : GrothendieckTopology C) (F : CartesianBasedFunctor p₁ p₂) :
    IsStackification J F ↔
      IsLocalEquivalence J F ∧ IsStack.OnSite J p₂ := sorry

/-- Lemma 8.9.1 (1), tag 02ZP: on every fiber, the canonical Hom-presheaf map of a
stackification presents its target as the sheafification of its source. The target sheaf
condition and membership in the localizing class are exposed separately by
`Presheaf.IsSheafification.isSheaf` and `Presheaf.IsSheafification.mem_W`. -/
@[stacks 02ZP "Hom-presheaf sheafification condition",
  stacks 02ZN "stackification Hom-presheaf sheafification condition"]
theorem IsStackification.homSheafification
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    (hF : IsStackification J F) {U : C} (x y : p₁.Fiber U) :
    Presheaf.IsSheafification (J.over U)
      (HomPresheaf.Chosen.map F x y) := sorry

/-- Any cartesian morphism from the source of a stackification to another stack factors through
the stackification, without requiring the three total categories to share universes. -/
@[stacks 0435 "heterogeneous stackification lift"]
theorem IsStackification.lift
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    (F : CartesianBasedFunctor p₁ p₃) :
    ∃ G : CartesianBasedFunctor p₂ p₃,
      Nonempty ((precomp p₃ i).obj G ≅ F) := sorry

attribute [stacks 0436 "factorization through a groupoid stackification"]
  IsStackification.lift

/-- Two heterogeneous lifts through a stackification are related by a unique isomorphism
compatible with their comparison isomorphisms. -/
@[stacks 0435 "uniqueness of heterogeneous stackification lifts"]
theorem IsStackification.liftIsoUnique
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    {F : CartesianBasedFunctor p₁ p₃}
    (G₁ G₂ : CartesianBasedFunctor p₂ p₃)
    (α₁ : (precomp p₃ i).obj G₁ ≅ F)
    (α₂ : (precomp p₃ i).obj G₂ ≅ F) :
    ∃! β : G₁ ≅ G₂, (precomp p₃ i).mapIso β ≪≫ α₂ = α₁ := sorry

attribute [stacks 0436 "unique comparison of heterogeneous groupoid-stackification lifts"]
  IsStackification.liftIsoUnique

namespace IsStackification

/-! The universal-property theorem above is intentionally proposition-valued.  The following
    owner packages a factorization and its comparison as reusable Type-valued data, while keeping
    the existential theorem and the noncanonical choice boundary explicit. -/

/-- A chosen factorization through a heterogeneous stackification.

The fields are the actual downstream data: a lift and its comparison after precomposition.  The
stackification proof is not stored again, so this is a thin data owner rather than a second
stackification predicate. -/
@[stacks 0435 "explicit heterogeneous stackification lift data"]
structure LiftChoice
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {i : CartesianBasedFunctor p₁ p₂}
    (F : CartesianBasedFunctor p₁ p₃) where
  /-- The cartesian functor factoring `F` through `i`. -/
  lift : CartesianBasedFunctor p₂ p₃
  /-- The comparison between the precomposed lift and `F`. -/
  comparison : (precomp p₃ i).obj lift ≅ F

attribute [stacks 0435 "heterogeneous stackification lift field"]
  LiftChoice.lift
attribute [stacks 0435 "heterogeneous stackification lift comparison field"]
  LiftChoice.comparison

/-- Package explicitly supplied lift and comparison data. -/
@[stacks 0435 "package heterogeneous stackification lift data"]
def LiftChoice.of
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {i : CartesianBasedFunctor p₁ p₂}
    {F : CartesianBasedFunctor p₁ p₃}
    (G : CartesianBasedFunctor p₂ p₃)
    (α : (precomp p₃ i).obj G ≅ F) : LiftChoice (i := i) F :=
  ⟨G, α⟩

/-- Convert the proposition-level existential lift theorem into a named data package.

This is the only helper that eliminates the existential; callers with an explicit lift should
prefer `LiftChoice.of`, which does not select any witness. -/
@[stacks 0435 "package an existential stackification lift"]
noncomputable def LiftChoice.ofExists
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {i : CartesianBasedFunctor p₁ p₂}
    {F : CartesianBasedFunctor p₁ p₃}
    (h : ∃ G : CartesianBasedFunctor p₂ p₃,
      Nonempty ((precomp p₃ i).obj G ≅ F)) : LiftChoice (i := i) F where
  lift := Classical.choose h
  comparison := Classical.choice (Classical.choose_spec h)

/-- The stackification universal property supplies a nonempty type of lift packages. -/
@[stacks 0435 "existence of heterogeneous stackification lift data"]
theorem LiftChoice.nonempty
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    (F : CartesianBasedFunctor p₁ p₃) :
    Nonempty (LiftChoice (i := i) F) := sorry

/-- A convenient selected lift obtained from the universal-property theorem.

This is noncanonical choice data.  Downstream statements should use its named fields and the
comparison/uniqueness API instead of unfolding the `Classical.choice` implementation. -/
@[stacks 0435 "selected heterogeneous stackification lift"]
noncomputable def liftChoice
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    (F : CartesianBasedFunctor p₁ p₃) : LiftChoice (i := i) F :=
  LiftChoice.ofExists (hi.lift F)

/-- The comparison carried by the selected heterogeneous lift.

This is a named data readout, not a second existential theorem: the comparison remains the field
owner of `LiftChoice`, while this definition gives callers a stable name when they use the
noncanonical convenience value. -/
@[stacks 0435 "selected heterogeneous stackification lift comparison"]
noncomputable def liftChoiceComparison
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    (F : CartesianBasedFunctor p₁ p₃) :
    (precomp p₃ i).obj (liftChoice hi F).lift ≅ F :=
  (liftChoice hi F).comparison

/-- Any two explicit lift choices have a unique compatible comparison. -/
@[stacks 0435 "existence and uniqueness of heterogeneous stackification lift comparisons"]
theorem LiftChoice.existsUniqueComparisonIso
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    {F : CartesianBasedFunctor p₁ p₃}
    (L₁ L₂ : LiftChoice (i := i) F) :
    ∃! β : L₁.lift ≅ L₂.lift,
      (precomp p₃ i).mapIso β ≪≫ L₂.comparison = L₁.comparison := sorry

/-- The canonical comparison between two explicit lift choices. -/
@[stacks 0435 "comparison of heterogeneous stackification lift choices"]
noncomputable def LiftChoice.comparisonIso
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    {F : CartesianBasedFunctor p₁ p₃}
    (L₁ L₂ : LiftChoice (i := i) F) : L₁.lift ≅ L₂.lift :=
  Classical.choose (ExistsUnique.exists
    (LiftChoice.existsUniqueComparisonIso hi L₁ L₂))

/-- The comparison of two lift choices has the expected precomposition compatibility. -/
@[stacks 0435 "comparison specification for heterogeneous stackification lift choices"]
theorem LiftChoice.comparisonIso_spec
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    {F : CartesianBasedFunctor p₁ p₃}
    (L₁ L₂ : LiftChoice (i := i) F) :
    (precomp p₃ i).mapIso (L₁.comparisonIso hi L₂) ≪≫ L₂.comparison = L₁.comparison := sorry

/-- Any compatible comparison between two lift choices equals the selected one. -/
@[stacks 0435 "uniqueness of selected heterogeneous stackification lift comparison"]
theorem LiftChoice.comparisonIso_unique
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃]
    {F : CartesianBasedFunctor p₁ p₃}
    (L₁ L₂ : LiftChoice (i := i) F)
    (β : L₁.lift ≅ L₂.lift)
    (hβ : (precomp p₃ i).mapIso β ≪≫ L₂.comparison = L₁.comparison) :
    β = L₁.comparisonIso hi L₂ := sorry

end IsStackification

/-- Heterogeneous precomposition by a stackification is an equivalence on cartesian
Hom-categories into every stack. -/
@[stacks 04W9 "heterogeneous universal property of stackification"]
theorem IsStackification.precomp_isEquivalence
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    {J : GrothendieckTopology C} {i : CartesianBasedFunctor p₁ p₂}
    (hi : IsStackification J i) [IsStack.OnSite J p₃] :
    (precomp p₃ i).IsEquivalence := sorry

attribute [stacks 0436 "heterogeneous Hom equivalence induced by groupoid stackification"]
  IsStackification.precomp_isEquivalence

/- Data audit: the heterogeneous `LiftChoice` and `LiftChoice.of` store only caller-supplied
non-Prop data. Any reported `sorryAx` is inherited from Prop-valued category, functor, and
coherence laws in those field types; no lift or comparison is synthesized by a placeholder.
`ofExists` and `liftChoice` are the documented proposition-to-data boundary; their consumers
should use `comparisonIso_spec` and `comparisonIso_unique` rather than unfold choice. -/

end CartesianBasedFunctor

namespace FiberedCategoryOver.Hom

variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- A morphism `i : X ⟶ Y` of fibred categories is a stackification of `X` when its cartesian
functor is a local equivalence and `Y` is a stack. This is the fixed-owner view of
`CartesianBasedFunctor.IsStackification`. -/
@[stacks 02ZM "fixed-universe stackification predicate"]
abbrev IsStackification (J : GrothendieckTopology C) (i : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.IsStackification J
    (FiberedCategoryOver.toCartesianBasedFunctor i)

/-- The fixed-owner stackification predicate is exactly local equivalence together with the target
stack condition. -/
@[stacks 02ZN "fixed-universe defining conditions of stackification"]
theorem IsStackification.iff_isLocalEquivalence_and_isStack
    (J : GrothendieckTopology C) (i : X ⟶ Y) :
    IsStackification J i ↔
      IsLocalEquivalence J i ∧ IsStack.OnSite J Y.p := sorry

/-- A fixed-universe stackification has a stack as its target projection.

This is the explicit readout counterpart of the instance carried by the heterogeneous owner.  It
is useful for downstream statements that want the target-stack hypothesis as an ordinary term
without relying on typeclass search or unfolding the fixed-universe abbreviation. -/
@[stacks 02ZN "fixed-universe target-stack readout"]
theorem IsStackification.isStack
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (h : IsStackification J i) :
    IsStack.OnSite J Y.p := sorry

/-- The universal property of stackification: any morphism to a stack factors through the
stackification. The stackification witness is an explicit method argument so a caller holding a
one-off witness need not install a local instance. -/
@[stacks 0435]
theorem IsStackification.lift
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y} (h : IsStackification J i)
    [IsStack.OnSite J Z.p] (F : X ⟶ Z) :
    ∃ G : Y ⟶ Z, Nonempty (i ≫ G ≅ F) := sorry

/-- Two factorizations through a stackification are related by a unique `2`-isomorphism
compatible with their comparison isomorphisms.

It remembers the chosen factorization cells and characterizes the comparison between the lifts,
rather than merely asserting that the two lifts are isomorphic. -/
@[stacks 0435 "uniqueness of fixed-universe stackification lifts"]
theorem IsStackification.liftIsoUnique
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y} (h : IsStackification J i)
    [IsStack.OnSite J Z.p] {F : X ⟶ Z}
    (G₁ G₂ : Y ⟶ Z) (α₁ : i ≫ G₁ ≅ F) (α₂ : i ≫ G₂ ≅ F) :
    ∃! β : G₁ ≅ G₂,
      (Bicategory.precomp Z i).mapIso β ≪≫ α₂ = α₁ := sorry

namespace IsStackification

/-! The fixed-universe choice owner mirrors the heterogeneous `CartesianBasedFunctor` API.  It is
    a thin bundled readout: the defining predicate remains the abbreviation above, and all
    noncanonical data is confined to this explicit choice boundary. -/

/-- A chosen factorization through a fixed-universe stackification. -/
@[stacks 0435 "explicit fixed-universe stackification lift data"]
structure LiftChoice
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {i : X ⟶ Y} (F : X ⟶ Z) where
  /-- The bundled lift through the stackification target. -/
  lift : Y ⟶ Z
  /-- The comparison after precomposition with the stackification map. -/
  comparison : i ≫ lift ≅ F

attribute [stacks 0435 "fixed-universe stackification lift field"] LiftChoice.lift
attribute [stacks 0435 "fixed-universe stackification lift comparison field"] LiftChoice.comparison

/-- Package explicitly supplied fixed-universe lift data. -/
@[stacks 0435 "package fixed-universe stackification lift data"]
def LiftChoice.of
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {i : X ⟶ Y} {F : X ⟶ Z}
    (G : Y ⟶ Z) (α : i ≫ G ≅ F) : LiftChoice (i := i) F :=
  ⟨G, α⟩

/-- Convert the fixed-universe lift existence theorem into one named data package. -/
@[stacks 0435 "package an existential fixed-universe stackification lift"]
noncomputable def LiftChoice.ofExists
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {i : X ⟶ Y} {F : X ⟶ Z}
    (h : ∃ G : Y ⟶ Z, Nonempty (i ≫ G ≅ F)) : LiftChoice (i := i) F where
  lift := Classical.choose h
  comparison := Classical.choice (Classical.choose_spec h)

/-- A fixed-universe stackification supplies a nonempty type of lift packages. -/
@[stacks 0435 "existence of fixed-universe stackification lift data"]
theorem LiftChoice.nonempty
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (hi : IsStackification J i) [IsStack.OnSite J Z.p]
    (F : X ⟶ Z) : Nonempty (LiftChoice (i := i) F) := sorry

/-- A convenient selected fixed-universe lift. -/
@[stacks 0435 "selected fixed-universe stackification lift"]
noncomputable def liftChoice
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (hi : IsStackification J i) [IsStack.OnSite J Z.p]
    (F : X ⟶ Z) : LiftChoice (i := i) F :=
  LiftChoice.ofExists (hi.lift F)

/-- The comparison carried by the selected fixed-universe lift. -/
@[stacks 0435 "selected fixed-universe stackification lift comparison"]
noncomputable def liftChoiceComparison
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (hi : IsStackification J i) [IsStack.OnSite J Z.p]
    (F : X ⟶ Z) : i ≫ (liftChoice hi F).lift ≅ F :=
  (liftChoice hi F).comparison

/-- Any two fixed-universe lift choices admit a unique compatible comparison. -/
@[stacks 0435 "existence and uniqueness of fixed-universe stackification lifts"]
theorem LiftChoice.existsUniqueComparisonIso
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (hi : IsStackification J i) [IsStack.OnSite J Z.p]
    {F : X ⟶ Z} (L₁ L₂ : LiftChoice (i := i) F) :
    ∃! β : L₁.lift ≅ L₂.lift,
      (Bicategory.precomp Z i).mapIso β ≪≫ L₂.comparison = L₁.comparison := sorry

/-- The selected comparison between two fixed-universe lift choices. -/
@[stacks 0435 "comparison of fixed-universe stackification lifts"]
noncomputable def LiftChoice.comparisonIso
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (hi : IsStackification J i) [IsStack.OnSite J Z.p]
    {F : X ⟶ Z} (L₁ L₂ : LiftChoice (i := i) F) : L₁.lift ≅ L₂.lift :=
  Classical.choose (ExistsUnique.exists
    (LiftChoice.existsUniqueComparisonIso hi L₁ L₂))

/-- The selected fixed-universe lift comparison has the expected compatibility equation. -/
@[stacks 0435 "specification of fixed-universe stackification lift comparison"]
theorem LiftChoice.comparisonIso_spec
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (hi : IsStackification J i) [IsStack.OnSite J Z.p]
    {F : X ⟶ Z} (L₁ L₂ : LiftChoice (i := i) F) :
    (Bicategory.precomp Z i).mapIso (LiftChoice.comparisonIso hi L₁ L₂) ≪≫
        L₂.comparison = L₁.comparison := sorry

/-- Any compatible fixed-universe lift comparison equals the selected one. -/
@[stacks 0435 "uniqueness of fixed-universe stackification lift comparison"]
theorem LiftChoice.comparisonIso_unique
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y}
    (hi : IsStackification J i) [IsStack.OnSite J Z.p]
    {F : X ⟶ Z} (L₁ L₂ : LiftChoice (i := i) F)
    (β : L₁.lift ≅ L₂.lift)
    (hβ : (Bicategory.precomp Z i).mapIso β ≪≫ L₂.comparison = L₁.comparison) :
    β = LiftChoice.comparisonIso hi L₁ L₂ := sorry

end IsStackification

/-- The fixed-owner specialization of the universal Hom-category property of stackification. -/
@[stacks 04W9 "fixed-universe Hom property of stackification"]
theorem IsStackification.precomp_isEquivalence
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {i : X ⟶ Y} (h : IsStackification J i)
    [IsStack.OnSite J Z.p] :
    (Bicategory.precomp Z i).IsEquivalence := sorry

/- Data audit: the fixed `LiftChoice` is the bundled specialization of the same explicit owner.
Any reported `sorryAx` is inherited from Prop-valued category, functor, and coherence laws in its
field types. Only `ofExists` and `liftChoice` cross from proposition-level existence to selected
data; no lift or comparison is synthesized by a placeholder. -/

end FiberedCategoryOver.Hom

end CategoryTheory
