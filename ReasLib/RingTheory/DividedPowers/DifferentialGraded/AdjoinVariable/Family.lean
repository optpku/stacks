/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.AdjoinVariable.Family

/-!
# Adjoining an indexed family to a divided-power chain DGA

This file generalizes the one-cell API to a possibly infinite family of generators in one positive
degree.  The attaching family, generator family, differential equations, relative lift, and
finite-subset descent maps are explicit.  Forgetting the differential recovers the neutral graded
adjoining-family presentation.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w x y

namespace DividedPowerChainAlgebra

variable {R : Type u} [CommRing R]

namespace Adjoin

/-- A relative indexed family of degree-`d` cells attached to `A` along `f`.

Maps out are exactly maps out of `A` together with a compatible image for every generator.  The
`gradedPresentation` field additionally asserts the corresponding universal property after
forgetting the differential, so downstream graded and chain constructions share one owner. -/
@[stacks 0F4I "indexed divided-power chain-DGA extension"]
structure Family (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    {J : Type w} (f : J → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)) where
  /-- Every attaching element is closed in the base chain DGA. -/
  attaching_isCycle (j : J) : IsCycle A d (f j)
  /-- The extended divided-power chain DGA. -/
  algebra : DividedPowerChainAlgebra.{u, v} R
  /-- The canonical inclusion of the base DGA. -/
  inclusion : A ⟶ algebra
  /-- The indexed homogeneous generators in degree `d`. -/
  generator : J → algebra.toChainDGAlgebra.nonnegativePiece (d : ℕ)
  /-- Every generator has differential given by its attaching element. -/
  differential_generator (j : J) :
    algebra.toChainDGAlgebra.nonnegativeDifferential d (generator j) =
      inclusion.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f j)
  /-- After forgetting the differential, the inclusion and generators form the relative free
  graded divided-power extension. -/
  gradedPresentation : DividedPowerGradedAlgebra.Adjoin.Presentation
    A.toGradedAlgebra algebra.toGradedAlgebra (d : ℕ) J inclusion.toGradedHom generator
  /-- The relative lift determined by compatible images of all generators. -/
  lift {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
      (x : J → C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
      (hx : ∀ j : J, C.toChainDGAlgebra.nonnegativeDifferential d (x j) =
        g.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f j)) :
    algebra ⟶ C
  /-- The relative lift restricts to the prescribed map on the base. -/
  lift_base {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
      (x : J → C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
      (hx : ∀ j : J, C.toChainDGAlgebra.nonnegativeDifferential d (x j) =
        g.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f j)) :
    inclusion ≫ lift g x hx = g
  /-- The relative lift has the prescribed value on every generator. -/
  lift_generator {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
      (x : J → C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
      (hx : ∀ j : J, C.toChainDGAlgebra.nonnegativeDifferential d (x j) =
        g.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f j)) (j : J) :
    (lift g x hx).toChainHom ((d : ℕ) : ℤ) (generator j) = x j
  /-- Maps out of the extension are determined by the base and every generator value. -/
  hom_ext {C : DividedPowerChainAlgebra.{u, v} R} (g h : algebra ⟶ C)
      (hbase : inclusion ≫ g = inclusion ≫ h)
      (hgenerator : ∀ j : J,
        g.toChainHom ((d : ℕ) : ℤ) (generator j) =
          h.toChainHom ((d : ℕ) : ℤ) (generator j)) :
    g = h

namespace Family

variable {A : DividedPowerChainAlgebra.{u, v} R} {d : ℕ+} {J : Type w}
variable {f : J → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}

/-- Forgetting the differential from an indexed cell family gives its explicit graded
adjoining-family model. -/
@[stacks 0F4I "forgetful graded family owner"]
def toGradedFamily (X : Family A d f) :
    DividedPowerGradedAlgebra.Adjoin.Family A.toGradedAlgebra (d : ℕ) J where
  algebra := X.algebra.toGradedAlgebra
  inclusion := X.inclusion.toGradedHom
  generator := X.generator
  presentation := X.gradedPresentation

/-- Forgetting the differential from a relative chain-DGA lift gives the relative lift supplied by
the stored graded presentation. -/
@[simp, stacks 0F4I "graded shadow of a chain-DGA family lift"]
theorem lift_toGradedHom (X : Family A d f)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : J → C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (hx : ∀ j : J, C.toChainDGAlgebra.nonnegativeDifferential d (x j) =
      g.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f j)) :
    (X.lift g x hx).toGradedHom = X.toGradedFamily.lift g.toGradedHom x := sorry

/-- The graded isomorphism obtained by forgetting the differential from an isomorphism of
divided-power chain DGAs. -/
def gradedIso (X : Family A d f) {B : DividedPowerChainAlgebra.{u, v} R}
    (e : X.algebra ≅ B) : X.algebra.toGradedAlgebra ≅ B.toGradedAlgebra :=
  (DividedPowerChainAlgebra.toGraded R).mapIso e

/-- Transporting a family generator along a chain-DGA isomorphism preserves its prescribed
differential. -/
theorem isoGenerator_differential (X : Family A d f)
    {B : DividedPowerChainAlgebra.{u, v} R} (e : X.algebra ≅ B) (j : J) :
    B.toChainDGAlgebra.nonnegativeDifferential d
        (e.hom.toChainHom ((d : ℕ) : ℤ) (X.generator j)) =
      (X.inclusion ≫ e.hom).toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f j) := sorry

/-- The transported base inclusion is the image of the original graded inclusion under the
forgotten chain-DGA isomorphism. -/
theorem inclusion_comp_gradedIso_hom (X : Family A d f)
    {B : DividedPowerChainAlgebra.{u, v} R} (e : X.algebra ≅ B) :
    X.inclusion.toGradedHom ≫ (X.gradedIso e).hom =
      (X.inclusion ≫ e.hom).toGradedHom := sorry

/-- The forgotten chain-DGA isomorphism sends each original generator to its transported
generator. -/
theorem gradedIso_hom_generator (X : Family A d f)
    {B : DividedPowerChainAlgebra.{u, v} R} (e : X.algebra ≅ B) (j : J) :
    (X.gradedIso e).hom.toGradedHom.map d (X.generator j) =
      e.hom.toChainHom ((d : ℕ) : ℤ) (X.generator j) := sorry

/-- Transport the stored graded presentation along an isomorphism of the underlying chain-DGA
family model. -/
@[stacks 0F4I "graded presentation transported along a chain-DGA isomorphism"]
def gradedPresentationOfIso (X : Family A d f)
    {B : DividedPowerChainAlgebra.{u, v} R} (e : X.algebra ≅ B) :
    DividedPowerGradedAlgebra.Adjoin.Presentation
      A.toGradedAlgebra B.toGradedAlgebra (d : ℕ) J
      (X.inclusion ≫ e.hom).toGradedHom
      (fun j ↦ e.hom.toChainHom ((d : ℕ) : ℤ) (X.generator j)) :=
  X.gradedPresentation.ofIso (X.gradedIso e)
    (X.inclusion ≫ e.hom).toGradedHom
    (fun j ↦ e.hom.toChainHom ((d : ℕ) : ℤ) (X.generator j))
    (X.inclusion_comp_gradedIso_hom e) (X.gradedIso_hom_generator e)

/-- Transport a relative chain-DGA lift backwards along an isomorphism of the family algebra. -/
def isoLift (X : Family A d f) {B : DividedPowerChainAlgebra.{u, v} R}
    (e : X.algebra ≅ B) {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : J → C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (hx : ∀ j : J, C.toChainDGAlgebra.nonnegativeDifferential d (x j) =
      g.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f j)) : B ⟶ C :=
  e.inv ≫ X.lift g x hx

/-- A transported relative lift restricts to the prescribed base map. -/
theorem inclusion_comp_isoLift (X : Family A d f)
    {B : DividedPowerChainAlgebra.{u, v} R} (e : X.algebra ≅ B)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : J → C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (hx : ∀ j : J, C.toChainDGAlgebra.nonnegativeDifferential d (x j) =
      g.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f j)) :
    (X.inclusion ≫ e.hom) ≫ X.isoLift e g x hx = g := sorry

/-- A transported relative lift sends every transported generator to its prescribed value. -/
theorem isoLift_generator (X : Family A d f)
    {B : DividedPowerChainAlgebra.{u, v} R} (e : X.algebra ≅ B)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : J → C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (hx : ∀ j : J, C.toChainDGAlgebra.nonnegativeDifferential d (x j) =
      g.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f j)) (j : J) :
    (X.isoLift e g x hx).toChainHom ((d : ℕ) : ℤ)
        (e.hom.toChainHom ((d : ℕ) : ℤ) (X.generator j)) = x j := sorry

/-- Maps out of an isomorphic family algebra are determined by the transported base and generator
data. -/
theorem isoHom_ext (X : Family A d f)
    {B : DividedPowerChainAlgebra.{u, v} R} (e : X.algebra ≅ B)
    {C : DividedPowerChainAlgebra.{u, v} R} (g h : B ⟶ C)
    (hbase : (X.inclusion ≫ e.hom) ≫ g = (X.inclusion ≫ e.hom) ≫ h)
    (hgenerator : ∀ j : J,
      g.toChainHom ((d : ℕ) : ℤ)
          (e.hom.toChainHom ((d : ℕ) : ℤ) (X.generator j)) =
        h.toChainHom ((d : ℕ) : ℤ)
          (e.hom.toChainHom ((d : ℕ) : ℤ) (X.generator j))) :
    g = h := sorry

/-- Transport an indexed chain-DGA adjoining-family model along an isomorphism of its algebra. -/
@[stacks 0F4I "transport of an indexed chain-DGA extension along an isomorphism"]
def ofIso (X : Family A d f) {B : DividedPowerChainAlgebra.{u, v} R}
    (e : X.algebra ≅ B) : Family A d f where
  attaching_isCycle := X.attaching_isCycle
  algebra := B
  inclusion := X.inclusion ≫ e.hom
  generator := fun j ↦ e.hom.toChainHom ((d : ℕ) : ℤ) (X.generator j)
  differential_generator := X.isoGenerator_differential e
  gradedPresentation := X.gradedPresentationOfIso e
  lift := X.isoLift e
  lift_base := X.inclusion_comp_isoLift e
  lift_generator := X.isoLift_generator e
  hom_ext := X.isoHom_ext e

/-- The algebra of a transported family is the target of the transporting isomorphism. -/
@[simp]
theorem ofIso_algebra (X : Family A d f) {B : DividedPowerChainAlgebra.{u, v} R}
    (e : X.algebra ≅ B) : (X.ofIso e).algebra = B := sorry

/-- The inclusion of a transported family is the original inclusion followed by the isomorphism. -/
@[simp]
theorem ofIso_inclusion (X : Family A d f) {B : DividedPowerChainAlgebra.{u, v} R}
    (e : X.algebra ≅ B) : (X.ofIso e).inclusion = X.inclusion ≫ e.hom := sorry

/-- The generators of a transported family are the images of the original generators. -/
@[simp]
theorem ofIso_generator (X : Family A d f) {B : DividedPowerChainAlgebra.{u, v} R}
    (e : X.algebra ≅ B) (j : J) :
    (X.ofIso e).generator j =
      e.hom.toChainHom ((d : ℕ) : ℤ) (X.generator j) := sorry

/-- The graded presentation stored by a transported family is the transported graded
presentation. -/
@[simp]
theorem ofIso_gradedPresentation (X : Family A d f)
    {B : DividedPowerChainAlgebra.{u, v} R} (e : X.algebra ≅ B) :
    (X.ofIso e).gradedPresentation = X.gradedPresentationOfIso e := sorry

/-- The lift stored by a transported family is the lift transported backwards along the
isomorphism. -/
@[simp]
theorem ofIso_lift (X : Family A d f) {B : DividedPowerChainAlgebra.{u, v} R}
    (e : X.algebra ≅ B) {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : J → C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (hx : ∀ j : J, C.toChainDGAlgebra.nonnegativeDifferential d (x j) =
      g.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f j)) :
    (X.ofIso e).lift g x hx = X.isoLift e g x hx := sorry

/-- Transporting a family along the identity isomorphism recovers the original family. -/
@[simp]
theorem ofIso_refl (X : Family A d f) : X.ofIso (Iso.refl X.algebra) = X := sorry

/-- Successive transports of a family agree with transport along the composite isomorphism. -/
@[simp]
theorem ofIso_trans (X : Family A d f) {B C : DividedPowerChainAlgebra.{u, v} R}
    (e : X.algebra ≅ B) (e' : B ≅ C) :
    (X.ofIso e).ofIso e' = X.ofIso (e.trans e') := sorry

/-- A constant value on `Unit` satisfies the singleton differential family exactly when that
value satisfies the one-cell differential equation. -/
theorem constant_differential
    {a : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (hx : C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) a) :
    ∀ _ : Unit, C.toChainDGAlgebra.nonnegativeDifferential d x =
      g.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) a := sorry

/-- Equality on the unique singleton generator gives equality on the whole `Unit`-indexed
generator family. -/
theorem unit_generator_ext
    {a : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    (X : Family A d (fun _ : Unit ↦ a)) {C : DividedPowerChainAlgebra.{u, v} R}
    (g h : X.algebra ⟶ C)
    (hgenerator : g.toChainHom ((d : ℕ) : ℤ) (X.generator ()) =
      h.toChainHom ((d : ℕ) : ℤ) (X.generator ())) :
    ∀ j : Unit, g.toChainHom ((d : ℕ) : ℤ) (X.generator j) =
      h.toChainHom ((d : ℕ) : ℤ) (X.generator j) := sorry

/-- A singleton indexed adjoining family, viewed as the corresponding one-cell extension. -/
@[stacks 09PM "singleton family as a divided-power chain-DGA cell"]
def toCell {a : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    (X : Family A d (fun _ : Unit ↦ a)) : Cell A d a where
  attaching_isCycle := X.attaching_isCycle ()
  algebra := X.algebra
  ι := X.inclusion
  generator := X.generator ()
  map_generator := X.differential_generator ()
  lift g x hx := X.lift g (fun _ ↦ x) (constant_differential g x hx)
  lift_base g x hx := X.lift_base g (fun _ ↦ x) (constant_differential g x hx)
  lift_generator g x hx :=
    X.lift_generator g (fun _ ↦ x) (constant_differential g x hx) ()
  hom_ext g h hbase hgenerator :=
    X.hom_ext g h hbase (unit_generator_ext X g h hgenerator)

/-- The algebra underlying the singleton-family cell is unchanged. -/
@[simp]
theorem toCell_algebra
    {a : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    (X : Family A d (fun _ : Unit ↦ a)) :
    X.toCell.algebra = X.algebra := sorry

/-- The inclusion of the singleton-family cell is the family inclusion. -/
@[simp]
theorem toCell_ι
    {a : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    (X : Family A d (fun _ : Unit ↦ a)) :
    X.toCell.ι = X.inclusion := sorry

/-- The generator of the singleton-family cell is its unique indexed generator. -/
@[simp]
theorem toCell_generator
    {a : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    (X : Family A d (fun _ : Unit ↦ a)) :
    X.toCell.generator = X.generator () := sorry

/-- A morphism out of an indexed cell family has prescribed base and generator values. -/
@[stacks 0F4I "relative lift specification for indexed chain-DGA extensions"]
structure IsLift (X : Family A d f) {C : DividedPowerChainAlgebra.{u, v} R}
    (g : A ⟶ C) (x : J → C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (h : X.algebra ⟶ C) : Prop where
  /-- The morphism restricts to the prescribed base map. -/
  base : X.inclusion ≫ h = g
  /-- The morphism has the prescribed value on every generator. -/
  generator (j : J) :
    h.toChainHom ((d : ℕ) : ℤ) (X.generator j) = x j

/-- The canonical relative lift satisfies its complete base-and-generator specification. -/
theorem lift_isLift (X : Family A d f) {C : DividedPowerChainAlgebra.{u, v} R}
    (g : A ⟶ C) (x : J → C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (hx : ∀ j : J, C.toChainDGAlgebra.nonnegativeDifferential d (x j) =
      g.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f j)) :
    X.IsLift g x (X.lift g x hx) := sorry

/-- A morphism satisfying the base-and-generator specification is the canonical relative lift. -/
theorem lift_unique (X : Family A d f) {C : DividedPowerChainAlgebra.{u, v} R}
    (g : A ⟶ C) (x : J → C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (hx : ∀ j : J, C.toChainDGAlgebra.nonnegativeDifferential d (x j) =
      g.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f j))
    (h : X.algebra ⟶ C) (hh : X.IsLift g x h) :
    h = X.lift g x hx := sorry

/-- Compatible images of an indexed attaching family admit a unique chain-DGA relative lift. -/
@[stacks 0F4I "relative mapping property for indexed chain-DGA extensions"]
theorem existsUnique_lift (X : Family A d f) {C : DividedPowerChainAlgebra.{u, v} R}
    (g : A ⟶ C) (x : J → C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (hx : ∀ j : J, C.toChainDGAlgebra.nonnegativeDifferential d (x j) =
      g.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f j)) :
    ∃! h : X.algebra ⟶ C, X.IsLift g x h := sorry

/-- Target generators satisfy the differential equations needed to reindex an adjoining family
along a map whose attaching maps commute. -/
theorem reindex_differential {K : Type x}
    {g : K → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    (Y : Family A d g) (σ : J → K) (hσ : g ∘ σ = f) (j : J) :
    Y.algebra.toChainDGAlgebra.nonnegativeDifferential d (Y.generator (σ j)) =
      Y.inclusion.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f j) := sorry

/-- Reindex an adjoining-family model along a map of index types compatible with the attaching
maps.  The source generator indexed by `j` is sent to the target generator indexed by `σ j`. -/
@[stacks 0F4I "reindexing map for indexed chain-DGA extensions"]
def reindex {K : Type x}
    {g : K → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    (X : Family A d f) (Y : Family A d g) (σ : J → K) (hσ : g ∘ σ = f) :
    X.algebra ⟶ Y.algebra :=
  X.lift Y.inclusion (fun j ↦ Y.generator (σ j)) (reindex_differential Y σ hσ)

/-- Reindexing is independent of the chosen proof that the attaching maps commute. -/
@[simp, stacks 0F4I "proof independence of chain-DGA family reindexing"]
theorem reindex_congr {K : Type x}
    {g : K → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    (X : Family A d f) (Y : Family A d g) (σ : J → K)
    (hσ hσ' : g ∘ σ = f) : X.reindex Y σ hσ = X.reindex Y σ hσ' := sorry

/-- Reindexing agrees with the target inclusion on the base. -/
@[simp]
theorem inclusion_comp_reindex {K : Type x}
    {g : K → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    (X : Family A d f) (Y : Family A d g) (σ : J → K) (hσ : g ∘ σ = f) :
    X.inclusion ≫ X.reindex Y σ hσ = Y.inclusion := sorry

/-- Reindexing sends every source generator to the target generator selected by the index map. -/
@[simp]
theorem reindex_generator {K : Type x}
    {g : K → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    (X : Family A d f) (Y : Family A d g) (σ : J → K) (hσ : g ∘ σ = f) (j : J) :
    (X.reindex Y σ hσ).toChainHom ((d : ℕ) : ℤ) (X.generator j) =
      Y.generator (σ j) := sorry

/-- Forgetting the differential identifies chain-DGA reindexing with graded reindexing. -/
@[simp, stacks 0F4I "graded shadow of chain-DGA family reindexing"]
theorem reindex_toGradedHom {K : Type x}
    {g : K → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    (X : Family A d f) (Y : Family A d g) (σ : J → K) (hσ : g ∘ σ = f) :
    (X.reindex Y σ hσ).toGradedHom = X.toGradedFamily.reindex Y.toGradedFamily σ := sorry

/-- Reindexing along the identity map is the identity morphism. -/
@[simp, stacks 0F4I "identity law for chain-DGA family reindexing"]
theorem reindex_id (X : Family A d f) :
    X.reindex X id rfl = 𝟙 X.algebra := sorry

/-- Compatibility of attaching maps is transitive under composition of index maps. -/
theorem reindex_comp_compatible {K : Type x} {L : Type y}
    {g : K → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    {h : L → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    (σ : J → K) (τ : K → L) (hσ : g ∘ σ = f) (hτ : h ∘ τ = g) :
    h ∘ (τ ∘ σ) = f := sorry

/-- Reindexing maps compose according to composition of compatible index maps. -/
@[stacks 0F4I "composition law for chain-DGA family reindexing"]
theorem reindex_comp {K : Type x} {L : Type y}
    {g : K → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    {h : L → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    (X : Family A d f) (Y : Family A d g) (Z : Family A d h)
    (σ : J → K) (τ : K → L) (hσ : g ∘ σ = f) (hτ : h ∘ τ = g) :
    X.reindex Y σ hσ ≫ Y.reindex Z τ hτ =
      X.reindex Z (τ ∘ σ) (reindex_comp_compatible σ τ hσ hτ) := sorry

/-- A map between two indexed cell-family models is a comparison when it preserves the base and
every indexed generator. -/
@[stacks 0F4I "comparison specification for indexed chain-DGA extensions"]
def IsComparison (X Y : Family A d f) (g : X.algebra ⟶ Y.algebra) : Prop :=
  X.IsLift Y.inclusion Y.generator g

/-- Being a comparison is exactly the base-and-generator specification. -/
@[simp]
theorem isComparison_iff (X Y : Family A d f) (g : X.algebra ⟶ Y.algebra) :
    IsComparison X Y g ↔ X.IsLift Y.inclusion Y.generator g := sorry

/-- The canonical comparison between two realizations of the same indexed cell family. -/
@[stacks 0F4I "comparison map for indexed chain-DGA extensions"]
def comparison (X Y : Family A d f) : X.algebra ⟶ Y.algebra :=
  X.reindex Y id rfl

/-- The canonical comparison satisfies the comparison specification. -/
@[stacks 0F4I "canonical comparison specification for indexed chain-DGA extensions"]
theorem comparison_isComparison (X Y : Family A d f) :
    IsComparison X Y (X.comparison Y) := sorry

/-- The canonical comparison agrees with the target inclusion on the base. -/
@[simp]
theorem inclusion_comp_comparison (X Y : Family A d f) :
    X.inclusion ≫ X.comparison Y = Y.inclusion := sorry

/-- The canonical comparison sends corresponding cell generators to one another. -/
@[simp]
theorem comparison_generator (X Y : Family A d f) (j : J) :
    (X.comparison Y).toChainHom ((d : ℕ) : ℤ) (X.generator j) = Y.generator j := sorry

/-- A chain-DGA map preserving the base and all generators is the canonical comparison. -/
theorem comparison_unique (X Y : Family A d f) (g : X.algebra ⟶ Y.algebra)
    (hbase : X.inclusion ≫ g = Y.inclusion)
    (hgenerator : ∀ j : J,
      g.toChainHom ((d : ℕ) : ℤ) (X.generator j) = Y.generator j) :
    g = X.comparison Y := sorry

namespace IsComparison

/-- Every map satisfying the comparison specification is the canonical comparison. -/
theorem eq {X Y : Family A d f} {g : X.algebra ⟶ Y.algebra}
    (hg : IsComparison X Y g) :
    g = X.comparison Y := sorry

end IsComparison

/-- There is a unique chain-DGA comparison between two indexed cell-family models. -/
@[stacks 0F4I "unique comparison for indexed chain-DGA extensions"]
theorem existsUnique_comparison (X Y : Family A d f) :
    ∃! g : X.algebra ⟶ Y.algebra, IsComparison X Y g := sorry

/-- The comparison from an indexed cell-family model to itself is the identity. -/
@[simp]
theorem comparison_self (X : Family A d f) :
    X.comparison X = 𝟙 X.algebra := sorry

/-- Canonical indexed cell-family comparisons compose transitively. -/
@[simp]
theorem comparison_comp (X Y Z : Family A d f) :
    X.comparison Y ≫ Y.comparison Z = X.comparison Z := sorry

/-- The forward and reverse comparisons compose to the identity on the source model. -/
theorem comparison_hom_inv_id (X Y : Family A d f) :
    X.comparison Y ≫ Y.comparison X = 𝟙 X.algebra := sorry

/-- The reverse and forward comparisons compose to the identity on the target model. -/
theorem comparison_inv_hom_id (X Y : Family A d f) :
    Y.comparison X ≫ X.comparison Y = 𝟙 Y.algebra := sorry

/-- The canonical isomorphism between two realizations of the same indexed cell family. -/
@[stacks 0F4I "canonical comparison of indexed chain-DGA extensions"]
def comparisonIso (X Y : Family A d f) : X.algebra ≅ Y.algebra where
  hom := X.comparison Y
  inv := Y.comparison X
  hom_inv_id := X.comparison_hom_inv_id Y
  inv_hom_id := X.comparison_inv_hom_id Y

/-- The forward map of the canonical family isomorphism is the comparison. -/
@[simp]
theorem comparisonIso_hom (X Y : Family A d f) :
    (X.comparisonIso Y).hom = X.comparison Y := sorry

/-- The inverse map of the canonical family isomorphism is the reverse comparison. -/
@[simp]
theorem comparisonIso_inv (X Y : Family A d f) :
    (X.comparisonIso Y).inv = Y.comparison X := sorry

/-- The canonical family isomorphism from a model to itself is the identity. -/
@[simp]
theorem comparisonIso_self (X : Family A d f) :
    X.comparisonIso X = Iso.refl X.algebra := sorry

/-- Reversing a canonical family isomorphism exchanges its two models. -/
@[simp]
theorem comparisonIso_symm (X Y : Family A d f) :
    (X.comparisonIso Y).symm = Y.comparisonIso X := sorry

/-- Canonical family isomorphisms compose transitively. -/
@[simp]
theorem comparisonIso_trans (X Y Z : Family A d f) :
    (X.comparisonIso Y).trans (Y.comparisonIso Z) = X.comparisonIso Z := sorry

/-- Forgetting the canonical chain comparison gives the canonical graded comparison. -/
@[simp, stacks 0F4I "graded shadow of the indexed chain-DGA comparison"]
theorem comparison_toGradedHom (X Y : Family A d f) :
    (X.comparison Y).toGradedHom = X.toGradedFamily.comparison Y.toGradedFamily := sorry

/-- Forgetting the differential from the canonical chain-DGA comparison gives the canonical graded
comparison isomorphism. -/
@[stacks 0F4I "graded shadow of the indexed chain-DGA comparison isomorphism"]
theorem comparisonIso_toGradedIso (X Y : Family A d f) :
    (DividedPowerChainAlgebra.toGraded R).mapIso (X.comparisonIso Y) =
      X.toGradedFamily.comparisonIso Y.toGradedFamily := sorry

/-- In odd degree, every generator in an indexed chain-DGA family has exterior square zero. -/
@[stacks 0F4I "odd chain-DGA family generators have exterior square zero"]
theorem generator_sq_eq_zero (X : Family A d f) (hd : Odd (d : ℕ)) (j : J) :
    GradedMonoid.GMul.mul (X.generator j) (X.generator j) = 0 := sorry

/-- Indexed cell-family models exist whenever every attaching element is closed.

Downstream declarations take an explicit `Family` model; no public definition chooses a witness
from this existence statement. -/
@[stacks 0F4I "existence of indexed divided-power chain-DGA extensions"]
theorem nonempty (A : DividedPowerChainAlgebra.{u, v} R) (d : ℕ+)
    {J : Type w} (f : J → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1))
    (hf : ∀ j : J, IsCycle A d (f j)) :
    Nonempty (Family A d f) := sorry

namespace FiniteSubset

variable {I : Type w}
variable {f : I → A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}

/-- The inclusion between the subtypes of two nested finite subsets. -/
def inclusion {E F : Finset I} (h : E ⊆ F) : E → F :=
  fun i ↦ ⟨i, h i.property⟩

/-- The transition map between indexed cell families on nested finite subsets. -/
@[stacks 0F4I "finite-subset transition for chain-DGA adjoining families"]
def map {E F : Finset I} (X : Family A d (fun i : E ↦ f i))
    (Y : Family A d (fun i : F ↦ f i)) (h : E ⊆ F) : X.algebra ⟶ Y.algebra :=
  X.reindex Y (inclusion h) rfl

/-- Forgetting the differential identifies a finite-subset transition with the graded transition. -/
@[simp, stacks 0F4I "graded shadow of a finite-subset chain-DGA transition"]
theorem map_toGradedHom {E F : Finset I}
    (X : Family A d (fun i : E ↦ f i))
    (Y : Family A d (fun i : F ↦ f i)) (h : E ⊆ F) :
    (map X Y h).toGradedHom =
      DividedPowerGradedAlgebra.Adjoin.Family.FiniteSubset.map
        X.toGradedFamily Y.toGradedFamily h := sorry

/-- A finite-subset transition agrees with the target inclusion on the base. -/
@[simp]
theorem inclusion_comp_map {E F : Finset I} (X : Family A d (fun i : E ↦ f i))
    (Y : Family A d (fun i : F ↦ f i)) (h : E ⊆ F) :
    X.inclusion ≫ map X Y h = Y.inclusion := sorry

/-- A finite-subset transition sends every generator to the corresponding target generator. -/
@[simp]
theorem map_generator {E F : Finset I} (X : Family A d (fun i : E ↦ f i))
    (Y : Family A d (fun i : F ↦ f i)) (h : E ⊆ F) (i : E) :
    (map X Y h).toChainHom ((d : ℕ) : ℤ) (X.generator i) =
      Y.generator (inclusion h i) := sorry

/-- Finite-subset transition maps compose according to inclusion. -/
theorem map_trans {E F G : Finset I} (X : Family A d (fun i : E ↦ f i))
    (Y : Family A d (fun i : F ↦ f i)) (Z : Family A d (fun i : G ↦ f i))
    (hEF : E ⊆ F) (hFG : F ⊆ G) :
    map X Y hEF ≫ map Y Z hFG = map X Z (hEF.trans hFG) := sorry

/-- Finite-subset transitions commute with the canonical comparison between two chain-DGA stage
systems. This square transports a finite-stage cocone across model choices. -/
@[stacks 0F4I "finite-subset comparison naturality for chain-DGA adjoining families"]
theorem comparison_naturality {E F : Finset I}
    (X_E Y_E : Family A d (fun i : E ↦ f i))
    (X_F Y_F : Family A d (fun i : F ↦ f i)) (h : E ⊆ F) :
    map X_E X_F h ≫ comparison X_F Y_F =
      comparison X_E Y_E ≫ map Y_E Y_F h := sorry

/-- The transition map attached to a reflexive finite-subset inclusion is the identity. -/
@[simp, stacks 0F4I "finite-subset chain-DGA transition identity"]
theorem map_refl {E : Finset I} (X : Family A d (fun i : E ↦ f i)) :
    map X X (le_refl E) = 𝟙 X.algebra := sorry

/-- The canonical map from a finite-subset model to the full indexed model. -/
@[stacks 0F4I "finite-subset map into an indexed chain-DGA family"]
def toIndexed (X : Family A d f) (E : Finset I)
    (Y : Family A d (fun i : E ↦ f i)) : Y.algebra ⟶ X.algebra :=
  Y.reindex X (fun i ↦ i.1) rfl

/-- Forgetting the differential identifies the finite-subset map into the indexed model with the
graded map into the corresponding graded family. -/
@[simp, stacks 0F4I "graded shadow of a finite-subset indexed map"]
theorem toIndexed_toGradedHom (X : Family A d f) (E : Finset I)
    (Y : Family A d (fun i : E ↦ f i)) :
    (toIndexed X E Y).toGradedHom =
      DividedPowerGradedAlgebra.Adjoin.Family.FiniteSubset.toIndexed
        X.toGradedFamily E Y.toGradedFamily := sorry

/-- The canonical map from a finite-subset model agrees with the full inclusion on the base. -/
@[simp]
theorem inclusion_comp_toIndexed (X : Family A d f) (E : Finset I)
    (Y : Family A d (fun i : E ↦ f i)) :
    Y.inclusion ≫ toIndexed X E Y = X.inclusion := sorry

/-- The canonical map from a finite-subset model sends each generator to the corresponding full
indexed generator. -/
@[simp]
theorem toIndexed_generator (X : Family A d f) (E : Finset I)
    (Y : Family A d (fun i : E ↦ f i)) (i : E) :
    (toIndexed X E Y).toChainHom ((d : ℕ) : ℤ) (Y.generator i) =
      X.generator i := sorry

/-- Maps from finite stages into an indexed chain-DGA family are natural along transitions. -/
@[simp, stacks 0F4I "finite-subset chain-DGA transition naturality"]
theorem toIndexed_comp_map {E F : Finset I} (Y : Family A d f)
    (X : Family A d (fun i : E ↦ f i)) (Z : Family A d (fun i : F ↦ f i)) (h : E ⊆ F) :
    map X Z h ≫ toIndexed Y F Z = toIndexed Y E X := sorry

/-- The canonical map from a finite stage commutes with comparison of the full and stage
chain-DGA models. This square transports a finite-stage cocone across both model choices. -/
@[stacks 0F4I "finite-stage chain-DGA comparison naturality"]
theorem toIndexed_comp_comparison {E : Finset I}
    (X Y : Family A d f)
    (X_E Y_E : Family A d (fun i : E ↦ f i)) :
    toIndexed X E X_E ≫ comparison X Y =
      comparison X_E Y_E ≫ toIndexed Y E Y_E := sorry

/-- Compatibility of maps defined on all finite-subset cell-family models. -/
@[stacks 0F4I "compatibility for finite-subset chain-DGA descent"]
def IsCompatible (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    {C : DividedPowerChainAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) : Prop :=
  ∀ (E F : Finset I) (h : E ⊆ F), map (X E) (X F) h ≫ φ F = φ E

/-- The compatibility predicate is exactly the finite-stage cocycle equation. -/
theorem isCompatible_iff {X : ∀ E : Finset I, Family A d (fun i : E ↦ f i)}
    {C : DividedPowerChainAlgebra.{u, v} R}
    {φ : ∀ E : Finset I, (X E).algebra ⟶ C} :
    IsCompatible X φ ↔
      ∀ (E F : Finset I) (h : E ⊆ F), map (X E) (X F) h ≫ φ F = φ E := sorry

/-- The base morphism extracted from a compatible finite-subset cocone. -/
@[stacks 0F4I "base component of finite-subset chain-DGA descent"]
def descBase (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    {C : DividedPowerChainAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) : A ⟶ C :=
  (X ∅).inclusion ≫ φ ∅

/-- The image of one indexed generator extracted from its singleton finite stage. -/
@[stacks 0F4I "generator component of finite-subset chain-DGA descent"]
def descGenerator (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    {C : DividedPowerChainAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) (i : I) :
    C.toChainDGAlgebra.nonnegativePiece (d : ℕ) :=
  (φ {i}).toChainHom ((d : ℕ) : ℤ)
    ((X {i}).generator ⟨i, Finset.mem_singleton_self i⟩)

/-- Generator values extracted from a compatible finite-subset cocone have the prescribed
differentials. -/
theorem descGenerator_differential
    (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    {C : DividedPowerChainAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) (hφ : IsCompatible X φ) (i : I) :
    C.toChainDGAlgebra.nonnegativeDifferential d (descGenerator X φ i) =
      (descBase X φ).toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) (f i) := sorry

/-- The explicit map descended from a compatible finite-subset cocone. -/
@[stacks 0F4I "finite-subset descent for chain-DGA adjoining families"]
def desc (Y : Family A d f)
    (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    {C : DividedPowerChainAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) (hφ : IsCompatible X φ) :
    Y.algebra ⟶ C :=
  Y.lift (descBase X φ) (descGenerator X φ) (descGenerator_differential X φ hφ)

/-- A map from the full indexed model descends a finite-subset cocone when it agrees after every
canonical finite-subset inclusion. -/
@[stacks 0F4I "descent specification for finite-subset chain-DGA cocones"]
def IsDesc (Y : Family A d f)
    (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    {C : DividedPowerChainAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) (g : Y.algebra ⟶ C) : Prop :=
  ∀ E : Finset I, toIndexed Y E (X E) ≫ g = φ E

/-- The descent predicate unfolds to agreement after every canonical finite-subset map. -/
theorem isDesc_iff {Y : Family A d f}
    {X : ∀ E : Finset I, Family A d (fun i : E ↦ f i)}
    {C : DividedPowerChainAlgebra.{u, v} R}
    {φ : ∀ E : Finset I, (X E).algebra ⟶ C} {g : Y.algebra ⟶ C} :
    IsDesc Y X φ g ↔
      ∀ (E : Finset I), toIndexed Y E (X E) ≫ g = φ E := sorry

/-- The explicit descended map agrees with the cocone at every finite stage. -/
theorem desc_isDesc (Y : Family A d f)
    (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    {C : DividedPowerChainAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) (hφ : IsCompatible X φ) :
    IsDesc Y X φ (desc Y X φ hφ) := sorry

/-- The descended chain-DGA map restricts to the compatible family at each finite stage. -/
@[simp, stacks 0F4I "finite-subset chain-DGA descent restriction"]
theorem desc_comp_toIndexed (Y : Family A d f)
    (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    {C : DividedPowerChainAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) (hφ : IsCompatible X φ) (E : Finset I) :
    toIndexed Y E (X E) ≫ desc Y X φ hφ = φ E := sorry

/-- The underlying graded map of a finite-subset descent is the graded descent of the underlying
finite-subset maps. -/
@[simp, stacks 0F4I "graded shadow of finite-subset chain-DGA descent"]
theorem desc_toGradedHom (Y : Family A d f)
    (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    {C : DividedPowerChainAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) (hφ : IsCompatible X φ) :
    (desc Y X φ hφ).toGradedHom =
      DividedPowerGradedAlgebra.Adjoin.Family.FiniteSubset.desc
        Y.toGradedFamily (fun E ↦ (X E).toGradedFamily)
        (fun E ↦ (φ E).toGradedHom) := sorry

/-- A map agreeing with a compatible finite-subset cocone is the explicit descended map. -/
theorem desc_unique (Y : Family A d f)
    (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    {C : DividedPowerChainAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) (hφ : IsCompatible X φ)
    (g : Y.algebra ⟶ C) (hg : IsDesc Y X φ g) :
    g = desc Y X φ hφ := sorry

/-- The full indexed cell-family model has the colimit universal property of its finite-subset
models. -/
@[stacks 0F4I "finite-subset colimit of indexed chain-DGA extensions"]
theorem existsUnique_desc (Y : Family A d f)
    (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    {C : DividedPowerChainAlgebra.{u, v} R}
    (φ : ∀ E : Finset I, (X E).algebra ⟶ C) (hφ : IsCompatible X φ) :
    ∃! g : Y.algebra ⟶ C, IsDesc Y X φ g := sorry

/-- The finite-subset diagram satisfies its identity law. -/
theorem diagram_map_id (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i)) (E : Finset I) :
    map (X E) (X E) (leOfHom (𝟙 E)) = 𝟙 (X E).algebra := sorry

/-- The finite-subset diagram satisfies its composition law. -/
theorem diagram_map_comp (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    {E F G : Finset I} (a : E ⟶ F) (b : F ⟶ G) :
    map (X E) (X G) (leOfHom (a ≫ b)) =
      map (X E) (X F) (leOfHom a) ≫ map (X F) (X G) (leOfHom b) := sorry

/-- The diagram of divided-power chain-DGA adjoining-family models on finite subsets. -/
@[stacks 0F4I "finite-subset chain-DGA adjoining-family diagram"]
noncomputable abbrev diagram (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i)) :
    Finset I ⥤ DividedPowerChainAlgebra.{u, v} R where
  obj E := (X E).algebra
  map h := map (X _) (X _) (leOfHom h)
  map_id := diagram_map_id X
  map_comp := diagram_map_comp X

/-- The stagewise canonical comparisons assemble into a natural isomorphism of finite-subset
chain-DGA diagrams.  The component maps are explicit; naturality and inverse laws are proof data. -/
@[stacks 0F4I "finite-subset chain-DGA diagram comparison isomorphism"]
noncomputable def comparisonNatIso
    (X Y : ∀ E : Finset I, Family A d (fun i : E ↦ f i)) : diagram X ≅ diagram Y :=
  NatIso.ofComponents (fun E ↦ comparisonIso (X E) (Y E))
    (fun {E F} a ↦ comparison_naturality
      (X E) (Y E) (X F) (Y F) (leOfHom a))

/-- The component of the finite-subset chain-DGA diagram comparison is the canonical stage map. -/
@[simp]
theorem comparisonNatIso_hom_app
    (X Y : ∀ E : Finset I, Family A d (fun i : E ↦ f i)) (E : Finset I) :
    (comparisonNatIso X Y).hom.app E = comparison (X E) (Y E) := sorry

/-- The inverse component of the finite-subset chain-DGA diagram comparison is the reverse stage
comparison. -/
@[simp]
theorem comparisonNatIso_inv_app
    (X Y : ∀ E : Finset I, Family A d (fun i : E ↦ f i)) (E : Finset I) :
    (comparisonNatIso X Y).inv.app E = comparison (Y E) (X E) := sorry

/-- The canonical finite-subset maps into an indexed chain-DGA family satisfy cocone naturality. -/
@[stacks 0F4I "finite-subset chain-DGA adjoining-family cocone naturality"]
theorem cocone_naturality (Y : Family A d f)
    (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i)) {E F : Finset I} (a : E ⟶ F) :
    map (X E) (X F) (leOfHom a) ≫ toIndexed Y F (X F) = toIndexed Y E (X E) := sorry

/-- The canonical cocone from finite-subset chain-DGA adjoining families to the indexed model. -/
@[stacks 0F4I "finite-subset chain-DGA adjoining-family cocone"]
noncomputable def cocone (Y : Family A d f)
    (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i)) : Cocone (diagram X) where
  pt := Y.algebra
  ι :=
    { app := fun E ↦ toIndexed Y E (X E)
      naturality := fun _ _ a ↦ cocone_naturality Y X a }

/-- The map represented by one leg of an arbitrary finite-subset chain-DGA cocone. -/
@[stacks 0F4I "finite-subset chain-DGA cocone leg"]
def coconeMap (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    (s : Cocone (diagram X)) (E : Finset I) : (X E).algebra ⟶ s.pt := s.ι.app E

/-- Every cocone on the finite-subset chain-DGA diagram gives a compatible family of maps. -/
theorem coconeMap_isCompatible (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    (s : Cocone (diagram X)) : IsCompatible X (coconeMap X s) := sorry

/-- The explicit morphism from an indexed chain-DGA family to the point of a finite-subset
cocone. -/
@[stacks 0F4I "finite-subset chain-DGA adjoining-family colimit morphism"]
noncomputable def colimitDesc (Y : Family A d f)
    (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i))
    (s : Cocone (diagram X)) : Y.algebra ⟶ s.pt :=
  desc Y X (coconeMap X s) (coconeMap_isCompatible X s)

/-- The explicit colimit morphism agrees with every supplied cocone leg. -/
@[simp]
theorem colimitDesc_fac (Y : Family A d f)
    (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i)) (s : Cocone (diagram X)) (E : Finset I) :
    (cocone Y X).ι.app E ≫ colimitDesc Y X s = s.ι.app E := sorry

/-- A morphism out of the indexed chain-DGA family is determined by all finite-stage legs. -/
theorem colimitDesc_unique (Y : Family A d f)
    (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i)) (s : Cocone (diagram X))
    (m : (cocone Y X).pt ⟶ s.pt)
    (hm : ∀ E : Finset I, (cocone Y X).ι.app E ≫ m = s.ι.app E) :
    m = colimitDesc Y X s := sorry

/-- The indexed chain-DGA family is the colimit of its finite-subset models. -/
@[stacks 0F4I "finite-subset chain-DGA adjoining-family colimit"]
noncomputable def isColimit (Y : Family A d f)
    (X : ∀ E : Finset I, Family A d (fun i : E ↦ f i)) : IsColimit (cocone Y X) where
  desc := colimitDesc Y X
  fac := colimitDesc_fac Y X
  uniq := colimitDesc_unique Y X

end FiniteSubset

end Family

namespace Cell

variable {A : DividedPowerChainAlgebra.{u, v} R} {d : ℕ+}
variable {a : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}

/-- The extra graded universal property needed to regard a one-cell extension as a singleton
indexed adjoining family.  A bare `Cell` controls chain-DGA maps only, so this datum is kept
explicit rather than inferred or chosen. -/
@[stacks 09PM "graded presentation of a divided-power chain-DGA cell"]
abbrev GradedPresentation (X : Cell A d a) :=
  DividedPowerGradedAlgebra.Adjoin.Presentation
    A.toGradedAlgebra X.algebra.toGradedAlgebra (d : ℕ) Unit X.ι.toGradedHom
      (fun _ ↦ X.generator)

/-- The one-cell attaching cycle supplies the cycle condition for the constant `Unit`-indexed
attaching family. -/
theorem unit_attaching_isCycle (X : Cell A d a) :
    ∀ _ : Unit, IsCycle A d a := sorry

/-- The one-cell differential equation supplies the differential equation for the constant
`Unit`-indexed generator family. -/
theorem unit_differential_generator (X : Cell A d a) :
    ∀ _ : Unit,
      X.algebra.toChainDGAlgebra.nonnegativeDifferential d X.generator =
        X.ι.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) a := sorry

/-- The one-cell lift sends the generator to every entry of a `Unit`-indexed assignment. -/
theorem unit_lift_generator (X : Cell A d a)
    {C : DividedPowerChainAlgebra.{u, v} R} (g : A ⟶ C)
    (x : Unit → C.toChainDGAlgebra.nonnegativePiece (d : ℕ))
    (hx : ∀ j : Unit, C.toChainDGAlgebra.nonnegativeDifferential d (x j) =
      g.toChainHom ((((d : ℕ) - 1 : ℕ) : ℤ)) a) (j : Unit) :
    (X.lift g (x ()) (hx ())).toChainHom ((d : ℕ) : ℤ) X.generator = x j := sorry

/-- A one-cell extension equipped with its graded-free presentation, viewed as a singleton
indexed adjoining family.  Requiring the graded presentation makes explicit the extra structure
carried by `Family` and avoids choosing or postulating it. -/
@[stacks 09PM "divided-power chain-DGA cell as a singleton family"]
def toFamily (X : Cell A d a) (presentation : X.GradedPresentation) :
    Family A d (fun _ : Unit ↦ a) where
  attaching_isCycle := unit_attaching_isCycle X
  algebra := X.algebra
  inclusion := X.ι
  generator := fun _ ↦ X.generator
  differential_generator := unit_differential_generator X
  gradedPresentation := presentation
  lift g x hx := X.lift g (x ()) (hx ())
  lift_base g x hx := X.lift_base g (x ()) (hx ())
  lift_generator g x hx j := unit_lift_generator X g x hx j
  hom_ext g h hbase hgenerator := X.hom_ext g h hbase (hgenerator ())

/-- The algebra underlying a cell viewed as a singleton family is unchanged. -/
@[simp]
theorem toFamily_algebra (X : Cell A d a)
    (presentation : X.GradedPresentation) :
    (X.toFamily presentation).algebra = X.algebra := sorry

/-- The inclusion of a cell viewed as a singleton family is its original inclusion. -/
@[simp]
theorem toFamily_inclusion (X : Cell A d a)
    (presentation : X.GradedPresentation) :
    (X.toFamily presentation).inclusion = X.ι := sorry

/-- Every generator of the singleton family obtained from a cell is its cell generator. -/
@[simp]
theorem toFamily_generator (X : Cell A d a) (presentation : X.GradedPresentation)
    (j : Unit) :
    (X.toFamily presentation).generator j = X.generator := sorry

/-- Converting a graded-presented cell to a singleton family and back recovers the cell. -/
@[simp, stacks 09PM "cell and singleton-family comparison"]
theorem toFamily_toCell (X : Cell A d a)
    (presentation : X.GradedPresentation) :
    (X.toFamily presentation).toCell = X := sorry

end Cell

namespace Family

/-- Converting a singleton family to a cell and restoring its stored graded presentation recovers
the original indexed family. -/
@[simp, stacks 09PM "singleton-family and cell comparison"]
theorem toCell_toFamily
    {A : DividedPowerChainAlgebra.{u, v} R} {d : ℕ+}
    {a : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}
    (X : Family A d (fun _ : Unit ↦ a)) :
    X.toCell.toFamily X.gradedPresentation = X := sorry

end Family

end Adjoin

end DividedPowerChainAlgebra
