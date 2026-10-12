/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_18_4_FiniteTypePoint
public import stacks_project.Chap107.Definition_107_6_3_LocalRingDim
public import stacks_project.Chap107.Remark_107_2_11
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dimension of the local ring via a presenting cogroupoid

In Situation 107.2.1, if the predeformation functor of a finite-type
field-valued point is presented by a coyoneda cogroupoid as in Remark 107.2.11,
the local-ring dimension at that point is `2 dim A - dim B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.AlgebraicStack (FieldValuedPoint)
open AlgebraicGeometry.GroupoidsOver.Predeformation
open FiberedCategoryOver.Groupoids
open CompleteLocalAlgCat
open GroupoidInFunctors
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
  [AlgebraicStack X]
  [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
  (x0 : FieldValuedPoint X)
  [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
  {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
  [Module.Finite Λ x0.K]
  (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
  [IsOpenImmersion openImmersion]
  (h_factor :
    Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
      x0.structureHom)

/-- A coyoneda cogroupoid `(ξ.base, B, s, t, c)` in `CompleteLocalAlgCat Λ k`
presents the predeformation functor of the formal object `ξ` after
restriction along `ArtinianLocalAlgCat.inclusion`, as in Remark 107.2.11 (4). -/
def IsPredeformationCogroupoid
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B) (c : B ⟶ pushout s t) : Prop :=
  ∃ (idMap : coyoneda.obj (op ξ.base) ⟶ coyoneda.obj (op B))
    (invMap : coyoneda.obj (op B) ⟶ coyoneda.obj (op B))
    (laws : CoyonedaGroupoidLaws s t c idMap invMap),
    Nonempty
      (GroupoidInFunctors.Iso
        (restrictInclusion (ofCoyoneda s t c idMap invMap laws))
        (ofFormalObject ξ))

/-- `IsPredeformationCogroupoid` means there exist identity and inverse maps making
`(s, t, c)` a coyoneda groupoid whose restriction is isomorphic to
`ofFormalObject ξ`. -/
theorem isPredeformationCogroupoid_iff
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B) (c : B ⟶ pushout s t) :
    IsPredeformationCogroupoid x0 openImmersion h_factor ξ B s t c ↔
      ∃ (idMap : coyoneda.obj (op ξ.base) ⟶ coyoneda.obj (op B))
        (invMap : coyoneda.obj (op B) ⟶ coyoneda.obj (op B))
        (laws : CoyonedaGroupoidLaws s t c idMap invMap),
        Nonempty
          (GroupoidInFunctors.Iso
            (restrictInclusion (ofCoyoneda s t c idMap invMap laws))
            (ofFormalObject ξ)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 107.6.4: Suppose that `X` is an algebraic stack, locally of finite type
over a locally Noetherian scheme `S`. Let `x0 : Spec(k) ⟶ X` be a morphism where
`k` is a field of finite type over `S`. Represent `ℱ_{X, k, x0}` as in
Remark 107.2.11 by a cogroupoid `(A, B, s, t, c)` of Noetherian complete local
`S`-algebras with residue field `k`, identifying `A` with `ξ.base` and `B` with
the kernel-pair algebra. Then the dimension of the local ring of `X` at `x0`
equals `dimensionDiff (ringKrullDim A + ringKrullDim A) (ringKrullDim B)`. -/
@[stacks 0DSB]
theorem localRingDimAt_eq_cogroupoid {S : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    [IsLocallyNoetherian X] (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
    [Module.Finite Λ x0.K]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
        x0.structureHom)
    (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ]
    (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B) (c : B ⟶ pushout s t)
    (h : IsPredeformationCogroupoid x0 openImmersion h_factor ξ B s t c)
    (hx : IsFiniteTypePoint (Points.mk x0)) :
    localRingDimAt (Points.mk x0) hx =
      dimensionDiff (ringKrullDim ξ.base.carrier + ringKrullDim ξ.base.carrier)
        (ringKrullDim B.carrier) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
