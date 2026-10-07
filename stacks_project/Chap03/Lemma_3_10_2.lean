module

public import stacks_project.Chap03.Lemma_3_10_1_ObjectProperty
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Cardinal

namespace Action

variable {G : Type u} [Group G]

/-- Lemma 3.10.2 (1). The left-regular `G`-set `leftRegular G` is an object of `P`. -/
@[stacks 000V]
theorem contains_leftRegular {P : ObjectProperty (Action (Type u) G)}
    (hP : IsSmallBoundClosed P) : P (leftRegular G) := sorry

/-- Lemma 3.10.2 (2). The product in `Action (Type u) G` of an at most countable family of objects
satisfying `P` is isomorphic to an object satisfying `P`. -/
@[stacks 000V]
theorem isoClosure_pi {P : ObjectProperty (Action (Type u) G)} (hP : IsSmallBoundClosed P)
    {ι : Type} [Countable ι] (S : ι → Action (Type u) G) (hS : ∀ i, P (S i)) :
    P.isoClosure (∏ᶜ S) := sorry

/-- An at most countable product of objects of the full subcategory of `P` exists. -/
theorem hasProduct {P : ObjectProperty (Action (Type u) G)} (hP : IsSmallBoundClosed P)
    {ι : Type} [Countable ι] (S : ι → P.FullSubcategory) : HasProduct S := sorry

/-- The canonical product comparison for `P.ι` is an isomorphism. -/
theorem isIso_piComparison {P : ObjectProperty (Action (Type u) G)} (hP : IsSmallBoundClosed P)
    {ι : Type} [Countable ι] (S : ι → P.FullSubcategory)
    [HasProduct S] [HasProduct (P.ι.obj ∘ S)] : IsIso (piComparison P.ι S) := sorry

/-- Lemma 3.10.2 (3). The coproduct in `Action (Type u) G` of an at most countable family of
objects satisfying `P` is isomorphic to an object satisfying `P`. -/
@[stacks 000V]
theorem isoClosure_sigma {P : ObjectProperty (Action (Type u) G)} (hP : IsSmallBoundClosed P)
    {ι : Type} [Countable ι] (S : ι → Action (Type u) G) (hS : ∀ i, P (S i)) :
    P.isoClosure (∐ S) := sorry

/-- An at most countable coproduct of objects of the full subcategory of `P` exists. -/
theorem hasCoproduct {P : ObjectProperty (Action (Type u) G)} (hP : IsSmallBoundClosed P)
    {ι : Type} [Countable ι] (S : ι → P.FullSubcategory) : HasCoproduct S := sorry

/-- The canonical coproduct comparison for `P.ι` is an isomorphism. -/
theorem isIso_sigmaComparison {P : ObjectProperty (Action (Type u) G)} (hP : IsSmallBoundClosed P)
    {ι : Type} [Countable ι] (S : ι → P.FullSubcategory)
    [HasCoproduct S] [HasCoproduct (P.ι.obj ∘ S)] : IsIso (sigmaComparison P.ι S) := sorry

/-- Lemma 3.10.2 (4). If `X`, `Y`, and `S` satisfy `P`, then the fibre product `pullback f g` in
`Action (Type u) G` is isomorphic to an object satisfying `P`. -/
@[stacks 000V]
theorem isoClosure_pullback {P : ObjectProperty (Action (Type u) G)} (hP : IsSmallBoundClosed P)
    {X Y S : Action (Type u) G} (hX : P X) (hY : P Y) (hS : P S) (f : X ⟶ S) (g : Y ⟶ S) :
    P.isoClosure (pullback f g) := sorry

/-- The fibre product of morphisms in the full subcategory of `P` exists. -/
theorem hasPullback {P : ObjectProperty (Action (Type u) G)} (hP : IsSmallBoundClosed P)
    {X Y S : P.FullSubcategory} (f : X ⟶ S) (g : Y ⟶ S) : HasPullback f g := sorry

/-- The canonical pullback comparison for `P.ι` is an isomorphism. -/
theorem isIso_pullbackComparison {P : ObjectProperty (Action (Type u) G)}
    (hP : IsSmallBoundClosed P) {X Y S : P.FullSubcategory} (f : X ⟶ S) (g : Y ⟶ S)
    [HasPullback f g] [HasPullback (P.ι.map f) (P.ι.map g)] :
    IsIso (pullbackComparison P.ι f g) := sorry

/-- Lemma 3.10.2 (5). If `X`, `Y`, and `Z` satisfy `P`, then the pushout `pushout f g` in
`Action (Type u) G` is isomorphic to an object satisfying `P`. -/
@[stacks 000V]
theorem isoClosure_pushout {P : ObjectProperty (Action (Type u) G)} (hP : IsSmallBoundClosed P)
    {X Y Z : Action (Type u) G} (hX : P X) (hY : P Y) (hZ : P Z) (f : X ⟶ Y) (g : X ⟶ Z) :
    P.isoClosure (pushout f g) := sorry

/-- The pushout of morphisms in the full subcategory of `P` exists. -/
theorem hasPushout {P : ObjectProperty (Action (Type u) G)} (hP : IsSmallBoundClosed P)
    {X Y Z : P.FullSubcategory} (f : X ⟶ Y) (g : X ⟶ Z) : HasPushout f g := sorry

/-- The canonical pushout comparison for `P.ι` is an isomorphism. -/
theorem isIso_pushoutComparison {P : ObjectProperty (Action (Type u) G)}
    (hP : IsSmallBoundClosed P) {X Y Z : P.FullSubcategory} (f : X ⟶ Y) (g : X ⟶ Z)
    [HasPushout f g] [HasPushout (P.ι.map f) (P.ι.map g)] :
    IsIso (pushoutComparison P.ι f g) := sorry

/-- The `G`-set structure on a `G`-stable subset of `U`. -/
def ofStableSubset (U : Action (Type u) G) (O : Set U.V)
    (hO : ∀ g : G, Set.MapsTo (fun x : U.V ↦ U.ρ g x) O O) : Action (Type u) G where
  V := O
  ρ :=
    { toFun g := ↾fun x ↦ ⟨U.ρ g x.1, hO g x.2⟩
      map_one' := sorry
      map_mul' := sorry }

/-- The inclusion of a `G`-stable subset as a morphism of `G`-sets. -/
def inclusion (U : Action (Type u) G) (O : Set U.V)
    (hO : ∀ g : G, Set.MapsTo (fun x : U.V ↦ U.ρ g x) O O) :
    ofStableSubset U O hO ⟶ U where
  hom := ↾Subtype.val
  comm := sorry

/-- The inclusion of a `G`-stable subset is a monomorphism. -/
theorem inclusion_mono (U : Action (Type u) G) (O : Set U.V)
    (hO : ∀ g : G, Set.MapsTo (fun x : U.V ↦ U.ρ g x) O O) :
    Mono (inclusion U O hO) := sorry

/-- The size of a `G`-stable subset is at most the size of the ambient `G`-set. -/
theorem size_ofStableSubset_le (U : Action (Type u) G) (O : Set U.V)
    (hO : ∀ g : G, Set.MapsTo (fun x : U.V ↦ U.ρ g x) O O) :
    size (ofStableSubset U O hO) ≤ size U := sorry

/-- Lemma 3.10.2 (6). A `G`-stable subset of an object satisfying `P` is isomorphic to an object
satisfying `P`. -/
@[stacks 000V]
theorem isoClosure_of_stableSubset {P : ObjectProperty (Action (Type u) G)}
    (hP : IsSmallBoundClosed P) {U : Action (Type u) G} (hU : P U) (O : Set U.V)
    (hO : ∀ g : G, Set.MapsTo (fun x : U.V ↦ U.ρ g x) O O) :
    P.isoClosure (ofStableSubset U O hO) := sorry

/-- A monomorphism into an object satisfying `P` has domain isomorphic to an object satisfying
`P`. -/
theorem isoClosure_of_mono {P : ObjectProperty (Action (Type u) G)} (hP : IsSmallBoundClosed P)
    {O U : Action (Type u) G} (hU : P U) (f : O ⟶ U) [Mono f] : P.isoClosure O := sorry

end Action

