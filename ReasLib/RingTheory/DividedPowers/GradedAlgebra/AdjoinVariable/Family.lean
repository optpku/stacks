module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.Data.Finset.Basic
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Category

/-!
# Adjoining an indexed family to a graded divided-power algebra

This file owns the relative universal property for adjoining a family of homogeneous generators in
one degree.  The parity of that degree is not baked into the owner: in odd degree the generators
have exterior behavior, while in even degree their divided monomials are controlled by the target
divided powers.  This is the reusable formal layer behind finite-subset constructions of Tate
algebras.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w x y

namespace DividedPowerGradedAlgebra

variable {R : Type u} [CommRing R]

namespace Adjoin

/-- The relative mapping property of a family of degree-`d` generators from `A` to `B`.

The inclusion and generator family are parameters, so the same presentation can be reused by a
graded algebra constructed directly or by forgetting the differential from a chain-DGA model. -/
@[stacks 0F4I "relative presentation for indexed graded extensions"]
structure Presentation (A B : DividedPowerGradedAlgebra.{u, v} R) (d : ℕ) (J : Type w)
    (inclusion : A ⟶ B) (generator : J → B.toGradedAlgebra.piece d) where
  /-- A degree-preserving assignment of the generators extends a prescribed map on the base. -/
  lift {C : DividedPowerGradedAlgebra.{u, v} R} (g : A ⟶ C)
      (x : J → C.toGradedAlgebra.piece d) : B ⟶ C
  /-- The relative lift restricts to the prescribed map on the base. -/
  lift_inclusion {C : DividedPowerGradedAlgebra.{u, v} R} (g : A ⟶ C)
      (x : J → C.toGradedAlgebra.piece d) :
    inclusion ≫ lift g x = g
  /-- The relative lift has the prescribed value on every generator. -/
  lift_generator {C : DividedPowerGradedAlgebra.{u, v} R} (g : A ⟶ C)
      (x : J → C.toGradedAlgebra.piece d) (j : J) :
    (lift g x).toGradedHom.map d (generator j) = x j
  /-- Maps out of the extension are determined by the base and all generator values. -/
  hom_ext {C : DividedPowerGradedAlgebra.{u, v} R} (g h : B ⟶ C)
      (hbase : inclusion ≫ g = inclusion ≫ h)
      (hgenerator : ∀ j : J,
        g.toGradedHom.map d (generator j) = h.toGradedHom.map d (generator j)) :
    g = h

namespace Presentation

variable {A B C : DividedPowerGradedAlgebra.{u, v} R} {d : ℕ} {J : Type w}
variable {inclusion : A ⟶ B} {generator : J → B.toGradedAlgebra.piece d}

/-- Transport the lift supplied by a presentation backwards along an isomorphism of its target
algebra. -/
def isoLift (P : Presentation A B d J inclusion generator) (e : B ≅ C)
    {D : DividedPowerGradedAlgebra.{u, v} R} (g : A ⟶ D)
    (x : J → D.toGradedAlgebra.piece d) : C ⟶ D :=
  e.inv ≫ P.lift g x

/-- A transported presentation lift restricts to the prescribed base map. -/
theorem inclusion_comp_isoLift (P : Presentation A B d J inclusion generator) (e : B ≅ C)
    {inclusion' : A ⟶ C} (h_inclusion : inclusion ≫ e.hom = inclusion')
    {D : DividedPowerGradedAlgebra.{u, v} R} (g : A ⟶ D)
    (x : J → D.toGradedAlgebra.piece d) :
    inclusion' ≫ P.isoLift e g x = g := sorry

/-- A transported presentation lift has the prescribed value on every transported generator. -/
theorem isoLift_generator (P : Presentation A B d J inclusion generator) (e : B ≅ C)
    {generator' : J → C.toGradedAlgebra.piece d}
    (h_generator : ∀ j, e.hom.toGradedHom.map d (generator j) = generator' j)
    {D : DividedPowerGradedAlgebra.{u, v} R} (g : A ⟶ D)
    (x : J → D.toGradedAlgebra.piece d) (j : J) :
    (P.isoLift e g x).toGradedHom.map d (generator' j) = x j := sorry

/-- Maps out of an isomorphic presentation target are determined by the transported base and
generator data. -/
theorem isoHom_ext (P : Presentation A B d J inclusion generator) (e : B ≅ C)
    {inclusion' : A ⟶ C} {generator' : J → C.toGradedAlgebra.piece d}
    (h_inclusion : inclusion ≫ e.hom = inclusion')
    (h_generator : ∀ j, e.hom.toGradedHom.map d (generator j) = generator' j)
    {D : DividedPowerGradedAlgebra.{u, v} R} (g h : C ⟶ D)
    (hbase : inclusion' ≫ g = inclusion' ≫ h)
    (hgenerator : ∀ j, g.toGradedHom.map d (generator' j) =
      h.toGradedHom.map d (generator' j)) :
    g = h := sorry

/-- Transport a relative adjoining-family presentation along an isomorphism of its target,
using explicit compatibility equations for the base inclusion and generators. -/
@[stacks 0F4I "transport of an indexed graded presentation along an isomorphism"]
def ofIso (P : Presentation A B d J inclusion generator) (e : B ≅ C)
    (inclusion' : A ⟶ C) (generator' : J → C.toGradedAlgebra.piece d)
    (h_inclusion : inclusion ≫ e.hom = inclusion')
    (h_generator : ∀ j, e.hom.toGradedHom.map d (generator j) = generator' j) :
    Presentation A C d J inclusion' generator' where
  lift := P.isoLift e
  lift_inclusion := P.inclusion_comp_isoLift e h_inclusion
  lift_generator := P.isoLift_generator e h_generator
  hom_ext := P.isoHom_ext e h_inclusion h_generator

end Presentation

/-- An explicit graded divided-power algebra obtained from `A` by adjoining a family of
degree-`d` generators, bundled with its relative universal property. -/
@[stacks 0F4I "indexed graded divided-power extension"]
structure Family (A : DividedPowerGradedAlgebra.{u, v} R) (d : ℕ) (J : Type w) where
  /-- The extended graded divided-power algebra. -/
  algebra : DividedPowerGradedAlgebra.{u, v} R
  /-- The canonical inclusion of the base algebra. -/
  inclusion : A ⟶ algebra
  /-- The indexed homogeneous generators. -/
  generator : J → algebra.toGradedAlgebra.piece d
  /-- The relative mapping property of the inclusion and generator family. -/
  presentation : Presentation A algebra d J inclusion generator

namespace Family

variable {A : DividedPowerGradedAlgebra.{u, v} R} {d : ℕ} {J : Type w}

/-- Package a supplied relative presentation as an indexed adjoining-family model.

This constructor keeps the carrier and generator data explicit while making the universal
property immediately available through the `Family` API. -/
@[stacks 0F4I "family constructed from a relative presentation"]
def ofPresentation {B : DividedPowerGradedAlgebra.{u, v} R}
    {inclusion : A ⟶ B} {generator : J → B.toGradedAlgebra.piece d}
    (P : Presentation A B d J inclusion generator) : Family A d J where
  algebra := B
  inclusion := inclusion
  generator := generator
  presentation := P

/-- The relative lift from an indexed adjoining-family model. -/
@[stacks 0F4I "relative lift for indexed graded extensions"]
def lift (X : Family A d J) {C : DividedPowerGradedAlgebra.{u, v} R} (g : A ⟶ C)
    (x : J → C.toGradedAlgebra.piece d) : X.algebra ⟶ C :=
  X.presentation.lift g x

/-- The relative lift restricts to the prescribed map on the base. -/
@[simp]
theorem inclusion_comp_lift (X : Family A d J)
    {C : DividedPowerGradedAlgebra.{u, v} R} (g : A ⟶ C)
    (x : J → C.toGradedAlgebra.piece d) :
    X.inclusion ≫ X.lift g x = g := sorry

/-- The relative lift sends every indexed generator to its prescribed value. -/
@[simp]
theorem lift_generator (X : Family A d J)
    {C : DividedPowerGradedAlgebra.{u, v} R} (g : A ⟶ C)
    (x : J → C.toGradedAlgebra.piece d) (j : J) :
    (X.lift g x).toGradedHom.map d (X.generator j) = x j := sorry

/-- A map out of an indexed adjoining-family model has specified base and generator values. -/
@[stacks 0F4I "relative lift specification for indexed graded extensions"]
structure IsLift (X : Family A d J) {C : DividedPowerGradedAlgebra.{u, v} R}
    (g : A ⟶ C) (x : J → C.toGradedAlgebra.piece d) (h : X.algebra ⟶ C) : Prop where
  /-- The map restricts to the prescribed base map. -/
  base : X.inclusion ≫ h = g
  /-- The map has the prescribed value on every generator. -/
  generator (j : J) : h.toGradedHom.map d (X.generator j) = x j

/-- The canonical relative lift satisfies its base and generator specification. -/
theorem lift_isLift (X : Family A d J) {C : DividedPowerGradedAlgebra.{u, v} R}
    (g : A ⟶ C) (x : J → C.toGradedAlgebra.piece d) :
    X.IsLift g x (X.lift g x) := sorry

/-- A map with the prescribed base and generator values is the canonical relative lift. -/
theorem lift_unique (X : Family A d J) {C : DividedPowerGradedAlgebra.{u, v} R}
    (g : A ⟶ C) (x : J → C.toGradedAlgebra.piece d) (h : X.algebra ⟶ C)
    (hh : X.IsLift g x h) :
    h = X.lift g x := sorry

/-- Base data and an indexed homogeneous assignment admit a unique relative lift. -/
@[stacks 0F4I "relative mapping property for indexed graded extensions"]
theorem existsUnique_lift (X : Family A d J) {C : DividedPowerGradedAlgebra.{u, v} R}
    (g : A ⟶ C) (x : J → C.toGradedAlgebra.piece d) :
    ∃! h : X.algebra ⟶ C, X.IsLift g x h := sorry

/-- Reindex an adjoining-family model along a map of index types.  The source generator indexed
by `j` is sent to the target generator indexed by `σ j`. -/
@[stacks 0F4I "reindexing map for indexed graded extensions"]
def reindex {K : Type x} (X : Family A d J) (Y : Family A d K) (σ : J → K) :
    X.algebra ⟶ Y.algebra :=
  X.lift Y.inclusion (fun j ↦ Y.generator (σ j))

/-- Reindexing agrees with the target inclusion on the base. -/
@[simp]
theorem inclusion_comp_reindex {K : Type x} (X : Family A d J) (Y : Family A d K)
    (σ : J → K) :
    X.inclusion ≫ X.reindex Y σ = Y.inclusion := sorry

/-- Reindexing sends each source generator to the target generator selected by the index map. -/
@[simp]
theorem reindex_generator {K : Type x} (X : Family A d J) (Y : Family A d K)
    (σ : J → K) (j : J) :
    (X.reindex Y σ).toGradedHom.map d (X.generator j) = Y.generator (σ j) := sorry

/-- Reindexing along the identity map is the identity morphism. -/
@[simp, stacks 0F4I "identity law for graded family reindexing"]
theorem reindex_id (X : Family A d J) :
    X.reindex X id = 𝟙 X.algebra := sorry

/-- Reindexing maps compose according to composition of their index maps. -/
@[stacks 0F4I "composition law for graded family reindexing"]
theorem reindex_comp {K : Type x} {L : Type y}
    (X : Family A d J) (Y : Family A d K) (Z : Family A d L)
    (σ : J → K) (τ : K → L) :
    X.reindex Y σ ≫ Y.reindex Z τ = X.reindex Z (τ ∘ σ) := sorry

/-- A map between two indexed family models is a comparison when it preserves the base and
every indexed generator. -/
@[stacks 0F4I "comparison specification for indexed graded extensions"]
def IsComparison (X Y : Family A d J) (g : X.algebra ⟶ Y.algebra) : Prop :=
  X.IsLift Y.inclusion Y.generator g

/-- Being a comparison is exactly the base-and-generator specification. -/
@[simp]
theorem isComparison_iff (X Y : Family A d J) (g : X.algebra ⟶ Y.algebra) :
    IsComparison X Y g ↔ X.IsLift Y.inclusion Y.generator g := sorry

/-- The canonical comparison between two realizations of the same adjoining family. -/
@[stacks 0F4I "comparison map for indexed graded extensions"]
def comparison (X Y : Family A d J) : X.algebra ⟶ Y.algebra :=
  X.reindex Y id

/-- The canonical comparison satisfies the comparison specification. -/
@[stacks 0F4I "canonical comparison specification for indexed graded extensions"]
theorem comparison_isComparison (X Y : Family A d J) :
    IsComparison X Y (X.comparison Y) := sorry

/-- The canonical comparison intertwines the two base inclusions. -/
@[simp]
theorem inclusion_comp_comparison (X Y : Family A d J) :
    X.inclusion ≫ X.comparison Y = Y.inclusion := sorry

/-- The canonical comparison sends corresponding generators to one another. -/
@[simp]
theorem comparison_generator (X Y : Family A d J) (j : J) :
    (X.comparison Y).toGradedHom.map d (X.generator j) = Y.generator j := sorry

/-- A morphism preserving the base inclusion and every generator is the canonical comparison. -/
theorem comparison_unique (X Y : Family A d J) (g : X.algebra ⟶ Y.algebra)
    (hbase : X.inclusion ≫ g = Y.inclusion)
    (hgenerator : ∀ j : J,
      g.toGradedHom.map d (X.generator j) = Y.generator j) :
    g = X.comparison Y := sorry

namespace IsComparison

/-- Every map satisfying the comparison specification is the canonical comparison. -/
theorem eq {X Y : Family A d J} {g : X.algebra ⟶ Y.algebra}
    (hg : IsComparison X Y g) :
    g = X.comparison Y := sorry

end IsComparison

/-- There is a unique graded comparison between two indexed family models. -/
@[stacks 0F4I "unique comparison for indexed graded extensions"]
theorem existsUnique_comparison (X Y : Family A d J) :
    ∃! g : X.algebra ⟶ Y.algebra, IsComparison X Y g := sorry

/-- The comparison from an adjoining-family model to itself is the identity. -/
@[simp]
theorem comparison_self (X : Family A d J) :
    X.comparison X = 𝟙 X.algebra := sorry

/-- Canonical adjoining-family comparisons compose transitively. -/
@[simp]
theorem comparison_comp (X Y Z : Family A d J) :
    X.comparison Y ≫ Y.comparison Z = X.comparison Z := sorry

/-- The forward and reverse comparisons compose to the identity on the source model. -/
theorem comparison_hom_inv_id (X Y : Family A d J) :
    X.comparison Y ≫ Y.comparison X = 𝟙 X.algebra := sorry

/-- The reverse and forward comparisons compose to the identity on the target model. -/
theorem comparison_inv_hom_id (X Y : Family A d J) :
    Y.comparison X ≫ X.comparison Y = 𝟙 Y.algebra := sorry

/-- The canonical isomorphism between two realizations of the same indexed adjoining family. -/
@[stacks 0F4I "canonical comparison of indexed graded extensions"]
def comparisonIso (X Y : Family A d J) : X.algebra ≅ Y.algebra where
  hom := X.comparison Y
  inv := Y.comparison X
  hom_inv_id := X.comparison_hom_inv_id Y
  inv_hom_id := X.comparison_inv_hom_id Y

/-- The forward map of the canonical family isomorphism is the comparison. -/
@[simp]
theorem comparisonIso_hom (X Y : Family A d J) :
    (X.comparisonIso Y).hom = X.comparison Y := sorry

/-- The inverse map of the canonical family isomorphism is the reverse comparison. -/
@[simp]
theorem comparisonIso_inv (X Y : Family A d J) :
    (X.comparisonIso Y).inv = Y.comparison X := sorry

/-- The canonical family isomorphism from a model to itself is the identity. -/
@[simp]
theorem comparisonIso_self (X : Family A d J) :
    X.comparisonIso X = Iso.refl X.algebra := sorry

/-- Reversing a canonical family isomorphism exchanges its two models. -/
@[simp]
theorem comparisonIso_symm (X Y : Family A d J) :
    (X.comparisonIso Y).symm = Y.comparisonIso X := sorry

/-- Canonical family isomorphisms compose transitively. -/
@[simp]
theorem comparisonIso_trans (X Y Z : Family A d J) :
    (X.comparisonIso Y).trans (Y.comparisonIso Z) = X.comparisonIso Z := sorry

/-- In odd degree, every adjoined generator has exterior square zero. -/
@[stacks 0F4I "odd adjoining generators have exterior square zero"]
theorem generator_sq_eq_zero (X : Family A d J) (hd : Odd d) (j : J) :
    GradedMonoid.GMul.mul (X.generator j) (X.generator j) = 0 := sorry

/-- A relative free graded divided-power extension exists for any indexed family in one degree.

The model remains explicit input to downstream constructions; this existence theorem does not
define a public choice of a carrier. -/
@[stacks 0F4I "existence of indexed graded divided-power extensions"]
theorem nonempty (A : DividedPowerGradedAlgebra.{u, v} R) (d : ℕ) (J : Type w) :
    Nonempty (Family A d J) := sorry

namespace FiniteSubset

variable {I : Type w}

/-- The inclusion of finite generator subtypes associated with `E ⊆ F`. -/
def inclusion {E F : Finset I} (h : E ⊆ F) : E → F :=
  fun i ↦ ⟨i, h i.property⟩

/-- The transition morphism between two finite-subset adjoining-family models. -/
@[stacks 0F4I "finite-subset transition for graded adjoining families"]
def map {E F : Finset I} (X : Family A d E) (Y : Family A d F) (h : E ⊆ F) :
    X.algebra ⟶ Y.algebra :=
  X.reindex Y (inclusion h)

/-- A finite-subset transition agrees with the target inclusion on the base. -/
@[simp]
theorem inclusion_comp_map {E F : Finset I} (X : Family A d E) (Y : Family A d F)
    (h : E ⊆ F) :
    X.inclusion ≫ map X Y h = Y.inclusion := sorry

/-- A finite-subset transition sends every source generator to the corresponding target
generator. -/
@[simp]
theorem map_generator {E F : Finset I} (X : Family A d E) (Y : Family A d F)
    (h : E ⊆ F) (i : E) :
    (map X Y h).toGradedHom.map d (X.generator i) = Y.generator (inclusion h i) := sorry

/-- Finite-subset transitions compose according to transitivity of inclusion. -/
theorem map_trans {E F G : Finset I} (X : Family A d E) (Y : Family A d F)
    (Z : Family A d G) (hEF : E ⊆ F) (hFG : F ⊆ G) :
    map X Y hEF ≫ map Y Z hFG = map X Z (hEF.trans hFG) := sorry

/-- Finite-subset transitions commute with the canonical comparison between two stage systems.
This is the square used to transport a finite-stage cocone across model choices. -/
@[stacks 0F4I "finite-subset comparison naturality for graded adjoining families"]
theorem comparison_naturality {E F : Finset I}
    (X_E Y_E : Family A d E) (X_F Y_F : Family A d F) (h : E ⊆ F) :
    map X_E X_F h ≫ comparison X_F Y_F =
      comparison X_E Y_E ≫ map Y_E Y_F h := sorry

/-- A finite-subset transition at a reflexive inclusion is the identity. -/
@[simp, stacks 0F4I "finite-subset transition identity"]
theorem map_refl {E : Finset I} (X : Family A d E) :
    map X X (le_refl E) = 𝟙 X.algebra := sorry

/-- The canonical map from a finite-subset model to an indexed model. -/
@[stacks 0F4I "finite-subset map into an indexed graded family"]
def toIndexed (X : Family A d J) (E : Finset J) (Y : Family A d E) :
    Y.algebra ⟶ X.algebra :=
  Y.reindex X fun i ↦ i.1

/-- The canonical map from a finite-subset model agrees with the full inclusion on the base. -/
@[simp]
theorem inclusion_comp_toIndexed (X : Family A d J) (E : Finset J) (Y : Family A d E) :
    Y.inclusion ≫ toIndexed X E Y = X.inclusion := sorry

/-- The map to the indexed model preserves every finite-subset generator. -/
@[simp]
theorem toIndexed_generator (X : Family A d J) (E : Finset J) (Y : Family A d E) (i : E) :
    (toIndexed X E Y).toGradedHom.map d (Y.generator i) = X.generator i := sorry

/-- Maps from finite stages into the indexed model are natural along finite-subset transitions. -/
@[simp, stacks 0F4I "finite-subset transition naturality"]
theorem toIndexed_comp_map {E F : Finset I} (Y : Family A d I)
    (X : Family A d E) (Z : Family A d F) (h : E ⊆ F) :
    map X Z h ≫ toIndexed Y F Z = toIndexed Y E X := sorry

/-- The canonical map from a finite stage commutes with comparison of the full and stage models.
This square transports a finite-stage cocone across both model choices. -/
@[stacks 0F4I "finite-stage comparison naturality"]
theorem toIndexed_comp_comparison {E : Finset I}
    (X Y : Family A d I) (X_E Y_E : Family A d E) :
    toIndexed X E X_E ≫ comparison X Y =
      comparison X_E Y_E ≫ toIndexed Y E Y_E := sorry

/-- Compatibility of maps defined on all finite-subset adjoining-family models. -/
@[stacks 0F4I "compatibility for finite-subset descent"]
def IsCompatible (X : ∀ E : Finset I, Family A d E)
    {C : DividedPowerGradedAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) : Prop :=
  ∀ (E F : Finset I) (h : E ⊆ F), map (X E) (X F) h ≫ φ F = φ E

/-- The compatibility predicate is exactly the finite-stage cocycle equation. -/
theorem isCompatible_iff {X : ∀ E : Finset I, Family A d E}
    {C : DividedPowerGradedAlgebra.{u, v} R}
    {φ : ∀ E : Finset I, (X E).algebra ⟶ C} :
    IsCompatible X φ ↔
      ∀ (E F : Finset I) (h : E ⊆ F), map (X E) (X F) h ≫ φ F = φ E := sorry

/-- The base morphism extracted from a finite-subset family of morphisms. -/
@[stacks 0F4I "base component of finite-subset descent"]
def descBase (X : ∀ E : Finset I, Family A d E)
    {C : DividedPowerGradedAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) : A ⟶ C :=
  (X ∅).inclusion ≫ φ ∅

/-- The image of one indexed generator extracted from its singleton finite stage. -/
@[stacks 0F4I "generator component of finite-subset descent"]
def descGenerator (X : ∀ E : Finset I, Family A d E)
    {C : DividedPowerGradedAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) (i : I) :
    C.toGradedAlgebra.piece d :=
  (φ {i}).toGradedHom.map d
    ((X {i}).generator ⟨i, Finset.mem_singleton_self i⟩)

/-- The explicit map induced by a finite-subset family of morphisms. Compatibility is used by the
descent specification theorems below. -/
@[stacks 0F4I "finite-subset descent for graded adjoining families"]
def desc (Y : Family A d I)
    (X : ∀ E : Finset I, Family A d E)
    {C : DividedPowerGradedAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) :
    Y.algebra ⟶ C :=
  Y.lift (descBase X φ) (descGenerator X φ)

/-- A map from the full indexed model descends a finite-subset cocone when it agrees after every
canonical finite-subset inclusion. -/
@[stacks 0F4I "descent specification for finite-subset cocones"]
def IsDesc (Y : Family A d I)
    (X : ∀ E : Finset I, Family A d E)
    {C : DividedPowerGradedAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) (g : Y.algebra ⟶ C) : Prop :=
  ∀ E : Finset I, toIndexed Y E (X E) ≫ g = φ E

/-- The descent predicate unfolds to agreement at every finite stage. -/
theorem isDesc_iff {Y : Family A d I}
    {X : ∀ E : Finset I, Family A d E}
    {C : DividedPowerGradedAlgebra.{u, v} R}
    {φ : ∀ E : Finset I, (X E).algebra ⟶ C} {g : Y.algebra ⟶ C} :
    IsDesc Y X φ g ↔
      ∀ E : Finset I, toIndexed Y E (X E) ≫ g = φ E := sorry

/-- The explicit descended map agrees with the cocone at every finite stage. -/
@[stacks 0F4I "finite-subset descent specification"]
theorem desc_isDesc (Y : Family A d I)
    (X : ∀ E : Finset I, Family A d E)
    {C : DividedPowerGradedAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) :
    IsCompatible X φ → IsDesc Y X φ (desc Y X φ) := sorry

/-- The descended map restricts to the compatible family at each finite stage. -/
@[simp, stacks 0F4I "finite-subset descent restriction"]
theorem desc_comp_toIndexed (Y : Family A d I)
    (X : ∀ E : Finset I, Family A d E)
    {C : DividedPowerGradedAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) (E : Finset I) :
    IsCompatible X φ → toIndexed Y E (X E) ≫ desc Y X φ = φ E := sorry

/-- A map agreeing with a compatible finite-subset cocone is the explicit descended map. -/
@[stacks 0F4I "finite-subset descent uniqueness"]
theorem desc_unique (Y : Family A d I)
    (X : ∀ E : Finset I, Family A d E)
    {C : DividedPowerGradedAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C)
    (g : Y.algebra ⟶ C) (hg : IsDesc Y X φ g) :
    g = desc Y X φ := sorry

/-- The full indexed adjoining-family model has the colimit universal property of its finite-subset
models. -/
@[stacks 0F4I "finite-subset colimit of indexed graded extensions"]
theorem existsUnique_desc (Y : Family A d I)
    (X : ∀ E : Finset I, Family A d E)
    {C : DividedPowerGradedAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) :
    IsCompatible X φ → ∃! g : Y.algebra ⟶ C, IsDesc Y X φ g := sorry

/-- The finite-subset diagram satisfies its identity law. -/
theorem diagram_map_id (X : ∀ E : Finset I, Family A d E) (E : Finset I) :
    map (X E) (X E) (leOfHom (𝟙 E)) = 𝟙 (X E).algebra := sorry

/-- The finite-subset diagram satisfies its composition law. -/
theorem diagram_map_comp (X : ∀ E : Finset I, Family A d E)
    {E F G : Finset I} (f : E ⟶ F) (g : F ⟶ G) :
    map (X E) (X G) (leOfHom (f ≫ g)) =
      map (X E) (X F) (leOfHom f) ≫ map (X F) (X G) (leOfHom g) := sorry

/-- The diagram of graded divided-power adjoining-family models on finite subsets. -/
@[stacks 0F4I "finite-subset graded adjoining-family diagram"]
noncomputable abbrev diagram (X : ∀ E : Finset I, Family A d E) :
    Finset I ⥤ DividedPowerGradedAlgebra.{u, v} R where
  obj E := (X E).algebra
  map f := map (X _) (X _) (leOfHom f)
  map_id := diagram_map_id X
  map_comp := diagram_map_comp X

/-- The stagewise canonical comparisons assemble into a natural isomorphism of finite-subset
diagrams.  The component maps are concrete; only naturality and the inverse laws are proof data. -/
@[stacks 0F4I "finite-subset diagram comparison isomorphism"]
noncomputable def comparisonNatIso
    (X Y : ∀ E : Finset I, Family A d E) : diagram X ≅ diagram Y :=
  NatIso.ofComponents (fun E ↦ comparisonIso (X E) (Y E))
    (fun {E F} a ↦ comparison_naturality
      (X E) (Y E) (X F) (Y F) (leOfHom a))

/-- The component of the finite-subset diagram comparison is the canonical stage comparison. -/
@[simp]
theorem comparisonNatIso_hom_app
    (X Y : ∀ E : Finset I, Family A d E) (E : Finset I) :
    (comparisonNatIso X Y).hom.app E = comparison (X E) (Y E) := sorry

/-- The inverse component of the finite-subset diagram comparison is the reverse stage comparison. -/
@[simp]
theorem comparisonNatIso_inv_app
    (X Y : ∀ E : Finset I, Family A d E) (E : Finset I) :
    (comparisonNatIso X Y).inv.app E = comparison (Y E) (X E) := sorry

/-- The canonical finite-subset maps into an indexed family satisfy cocone naturality. -/
@[stacks 0F4I "finite-subset graded adjoining-family cocone naturality"]
theorem cocone_naturality (Y : Family A d I)
    (X : ∀ E : Finset I, Family A d E) {E F : Finset I} (f : E ⟶ F) :
    map (X E) (X F) (leOfHom f) ≫ toIndexed Y F (X F) = toIndexed Y E (X E) := sorry

/-- The canonical cocone from finite-subset graded adjoining families to the indexed model. -/
@[stacks 0F4I "finite-subset graded adjoining-family cocone"]
noncomputable def cocone (Y : Family A d I)
    (X : ∀ E : Finset I, Family A d E) : Cocone (diagram X) where
  pt := Y.algebra
  ι :=
    { app := fun E ↦ toIndexed Y E (X E)
      naturality := fun _ _ f ↦ cocone_naturality Y X f }

/-- The map represented by one leg of an arbitrary finite-subset cocone. -/
@[stacks 0F4I "finite-subset graded cocone leg"]
def coconeMap (X : ∀ E : Finset I, Family A d E)
    (s : Cocone (diagram X)) (E : Finset I) : (X E).algebra ⟶ s.pt := s.ι.app E

/-- Every cocone on the finite-subset diagram gives a compatible family of maps. -/
theorem coconeMap_isCompatible (X : ∀ E : Finset I, Family A d E)
    (s : Cocone (diagram X)) : IsCompatible X (coconeMap X s) := sorry

/-- The explicit morphism from an indexed family to the point of a finite-subset cocone. -/
@[stacks 0F4I "finite-subset graded adjoining-family colimit morphism"]
noncomputable def colimitDesc (Y : Family A d I)
    (X : ∀ E : Finset I, Family A d E) (s : Cocone (diagram X)) : Y.algebra ⟶ s.pt :=
  desc Y X (coconeMap X s)

/-- The explicit colimit morphism agrees with every supplied cocone leg. -/
@[simp]
theorem colimitDesc_fac (Y : Family A d I)
    (X : ∀ E : Finset I, Family A d E) (s : Cocone (diagram X)) (E : Finset I) :
    (cocone Y X).ι.app E ≫ colimitDesc Y X s = s.ι.app E := sorry

/-- A morphism out of the indexed family is determined by all finite-stage legs. -/
theorem colimitDesc_unique (Y : Family A d I)
    (X : ∀ E : Finset I, Family A d E) (s : Cocone (diagram X))
    (m : (cocone Y X).pt ⟶ s.pt)
    (hm : ∀ E : Finset I, (cocone Y X).ι.app E ≫ m = s.ι.app E) :
    m = colimitDesc Y X s := sorry

/-- The indexed graded adjoining-family model is the colimit of its finite-subset models. -/
@[stacks 0F4I "finite-subset graded adjoining-family colimit"]
noncomputable def isColimit (Y : Family A d I)
    (X : ∀ E : Finset I, Family A d E) : IsColimit (cocone Y X) where
  desc := colimitDesc Y X
  fac := colimitDesc_fac Y X
  uniq := colimitDesc_unique Y X

end FiniteSubset

end Family

end Adjoin

end DividedPowerGradedAlgebra
