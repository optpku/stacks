/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Lemma_94_9_8
public import stacks_project.Chap94.Lemma_94_16_1_Groupoid
public import stacks_project.Chap94.Lemma_94_17_2
public import stacks_project.Chap94.Theorem_94_17_3
public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap100.Lemma_100_9_8_Restrict

/-!
# Invariant locally closed subspace cut out by an immersion into a quotient stack

The 2-fibre product `U' = U ×_[U / R] Z` of the quotient atlas against an immersion
`i : Z ⟶ [U / R]` is representable by an algebraic space. Recovering the first
projection yields an immersion `U' ⟶ U`, hence a locally closed subspace of `U`.
Closed and open immersions yield closed and open subspaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.TwoFibreProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The 2-fibre product `U' = U ×_[U / R] Z` of the quotient atlas against `i`. -/
def objectApex {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {Z : GroupoidsOver S} (i : Z ⟶ G.quotientStack) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} G.atlas i

/-- `objectApex` is the chosen 2-fibre product of `G.atlas` against `i`. -/
theorem objectApex_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {Z : GroupoidsOver S} (i : Z ⟶ G.quotientStack) :
    objectApex G i = TwoFibreProduct.apex.{u + 1, u, u + 1, u} G.atlas i :=
  sorry

/-- Space-representability of `U' = U ×_[U / R] Z`, by base change of the atlas along the
immersion `i`. -/
abbrev objectApex_isRepresentable {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    IsRepresentableByAlgebraicSpace (objectApex G i) :=
  IsRepresentableByAlgebraicSpace.twoFibreProduct i G.atlas
    (Immersion.relativelyRepresentable i)
    (IsRepresentableByAlgebraicSpace.of_toGroupoids G.U.left)

/-- The algebraic space representing `U' = U ×_[U / R] Z`. -/
def objectSpace {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ G.quotientStack)
    [Immersion i] : AlgebraicSpace S :=
  AlgebraicStack.representingSpace (objectApex_isRepresentable G i)

/-- `objectSpace` is the chosen representing algebraic space of `objectApex`. -/
theorem objectSpace_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    objectSpace G i = AlgebraicStack.representingSpace (objectApex_isRepresentable G i) :=
  sorry

/-- The recovered inclusion `U' ⟶ U` of algebraic spaces, obtained from the first projection of
the 2-fibre product. -/
def objectInclusion {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ G.quotientStack)
    [Immersion i] : objectSpace G i ⟶ G.U.left :=
  toGroupoids.recover (AlgebraicStack.representingEquiv (objectApex_isRepresentable G i))
    (Bicategory.Equivalence.id _)
    (TwoFibreProduct.fst.{u + 1, u, u + 1, u} G.atlas i)

/-- `objectInclusion` is recovered from the first projection of `G.atlas` against `i`. -/
theorem objectInclusion_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    objectInclusion G i =
      toGroupoids.recover (AlgebraicStack.representingEquiv (objectApex_isRepresentable G i))
        (Bicategory.Equivalence.id _)
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} G.atlas i) :=
  sorry

/-- The recovered inclusion `U' ⟶ U` is an immersion of algebraic spaces. -/
instance instIsImmersion_objectInclusion {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    AlgebraicSpace.IsImmersion (objectInclusion G i) :=
  sorry

/-- The recovered inclusion is an immersion, hence a monomorphism. -/
theorem isImmersion_objectInclusion_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    AlgebraicSpace.IsImmersion (objectInclusion G i) ∧ Mono (objectInclusion G i) :=
  sorry

/-- The canonical `R`-invariant locally closed subspace `Z ⊂ U` cut out by the immersion
`i : Z ⟶ [U / R]`. -/
def subspace {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ G.quotientStack)
    [Immersion i] : LocallyClosedSubspace G.U.left :=
  LocallyClosedSubspace.ofι (objectInclusion G i)

/-- The inclusion of `subspace G i` is the recovered 2-fibre-product projection. -/
theorem subspace_ι {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ G.quotientStack)
    [Immersion i] : (subspace G i).ι = objectInclusion G i :=
  sorry

/-- The underlying algebraic space of `subspace G i` is `objectSpace G i`. -/
theorem subspace_X {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ G.quotientStack)
    [Immersion i] : (subspace G i).X = objectSpace G i :=
  sorry

/-- The locally closed subspace cut out by `i` is `R`-invariant. -/
theorem isLocallyClosedInvariant_subspace {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    G.IsLocallyClosedInvariant (subspace G i) :=
  sorry

/-- The recovered inclusion `U' ⟶ U` is a closed immersion when `i` is a closed immersion. -/
instance instIsClosedImmersion_objectInclusion {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [ClosedImmersion i] :
    AlgebraicSpace.IsClosedImmersion (objectInclusion G i) :=
  sorry

/-- The recovered inclusion is a closed immersion, hence a monomorphism. -/
theorem isClosedImmersion_objectInclusion_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [ClosedImmersion i] :
    AlgebraicSpace.IsClosedImmersion (objectInclusion G i) ∧ Mono (objectInclusion G i) :=
  sorry

/-- The closed subspace `Z ⊂ U` cut out by a closed immersion `i : Z ⟶ [U / R]`. -/
def closedSubspace {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ G.quotientStack)
    [ClosedImmersion i] : ClosedSubspace G.U.left :=
  ClosedSubspace.ofι (objectInclusion G i)

/-- Passing `closedSubspace G i` to a locally closed subspace recovers `subspace G i`. -/
theorem closedSubspace_toLocallyClosed {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [ClosedImmersion i] :
    (closedSubspace G i).toLocallyClosed = subspace G i :=
  sorry

/-- The recovered inclusion `U' ⟶ U` is an open immersion when `i` is an open immersion. -/
instance instIsOpenImmersion_objectInclusion {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [OpenImmersion i] :
    AlgebraicSpace.IsOpenImmersion (objectInclusion G i) :=
  sorry

/-- The recovered inclusion is an open immersion, hence a monomorphism. -/
theorem isOpenImmersion_objectInclusion_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [OpenImmersion i] :
    AlgebraicSpace.IsOpenImmersion (objectInclusion G i) ∧ Mono (objectInclusion G i) :=
  sorry

/-- The open subspace `Z ⊂ U` cut out by an open immersion `i : Z ⟶ [U / R]`. -/
def openSubspace {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z] (i : Z ⟶ G.quotientStack)
    [OpenImmersion i] : OpenSubspace G.U.left :=
  OpenSubspace.ofι (objectInclusion G i)

/-- Passing `openSubspace G i` to a locally closed subspace recovers `subspace G i`. -/
theorem openSubspace_toLocallyClosed {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [OpenImmersion i] :
    (openSubspace G i).toLocallyClosed = subspace G i :=
  sorry

/-- The open subspace cut out by an open immersion is open-invariant. -/
theorem isOpenInvariant_openSubspace {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [OpenImmersion i] :
    G.IsOpenInvariant (openSubspace G i) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
