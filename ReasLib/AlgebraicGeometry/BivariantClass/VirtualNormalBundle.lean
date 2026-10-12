/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback
public import ReasLib.AlgebraicGeometry.BivariantClass.OpenRestriction.Completion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.VirtualNormalBundle
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.RankLocus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.OpenImmersion

/-!
# Bivariant classes of virtual normal bundles

A compatible assignment of completed virtual-normal classes to closed immersions extends to
immersions by composing with degree-zero flat pullback along the open part of a closed-open
factorization.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- A scheme morphism over `S`, with its source structure map recorded explicitly. -/
def overHom {S Z X : Scheme.{u}} (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X)
    (hi : i ≫ p = q) : Over.mk q ⟶ Over.mk p :=
  Over.homMk i hi

/-- The underlying scheme morphism of `overHom q p i hi` is `i`. -/
theorem overHom_left {S Z X : Scheme.{u}} (q : Z ⟶ S) (p : X ⟶ S)
    (i : Z ⟶ X) (hi : i ≫ p = q) : (overHom q p i hi).left = i := sorry

/-- The morphism over a base induced by a closed immersion is a closed immersion on
underlying schemes. -/
instance overHom_isClosedImmersion
    {S Z X : Scheme.{u}} (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X)
    (hi : i ≫ p = q) [IsClosedImmersion i] :
    IsClosedImmersion (overHom q p i hi).left := sorry

/-- The rank-`r` open of the module underlying a virtual normal bundle. -/
noncomputable def rankOpen {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ) : Z.Opens :=
  (@Scheme.Modules.rankClopen Z V.module V.isFiniteLocallyFree r).toOpens

/-- The rank open is the open associated to the canonical clopen rank locus. -/
theorem rankOpen_def {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ) :
    rankOpen i V r =
      (@Scheme.Modules.rankClopen Z V.module V.isFiniteLocallyFree r).toOpens := sorry

/-- Every rank open maps into the top open of the target. -/
theorem rankOpen_le_preimage_top {S Z X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    [IsImmersion i] (V : VirtualNormalBundle i) (r : ℕ) :
    rankOpen i V r ≤ (overHom q p i hi).left ⁻¹ᵁ (⊤ : X.Opens) := sorry

/-- The componentwise completion of bivariant classes for a virtual normal bundle, indexed
by the rank loci of its underlying finite locally free module. -/
abbrev CompletedClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsImmersion i]
    (V : VirtualNormalBundle i) : Type (u + 1) :=
  BivariantClass.OpenRestriction.Completion delta (overHom q p i hi)
    (fun r : ℕ ↦ @rankOpen Z X i h_i V r) (fun _ : Unit ↦ ⊤)
    (fun _ ↦ Unit.unit) (fun r ↦ rankOpen_le_preimage_top q p i hi V r)

/-- The equality of structure maps induced by a closed-open factorization. -/
theorem factorization_over {S Z U X : Scheme.{u}}
    (q : Z ⟶ S) (p : X ⟶ S) (i : Z ⟶ X) (hi : i ≫ p = q)
    (j : Z ⟶ U) (k : U ⟶ X) (h : j ≫ k = i) :
    j ≫ (k ≫ p) = q := sorry

/-- On each rank locus, composing the restricted closed and open morphisms gives the
restricted original immersion. -/
theorem factorizationRestrictionHom_eq
    {S Z U X : Scheme.{u}} (q : Z ⟶ S) (p : X ⟶ S)
    (i : Z ⟶ X) (hi : i ≫ p = q) (j : Z ⟶ U) (k : U ⟶ X)
    (h : j ≫ k = i) [h_i : IsImmersion i] [h_j : IsClosedImmersion j]
    [h_k : IsOpenImmersion k]
    (V : VirtualNormalBundle i) (r : ℕ) :
    BivariantClass.ComponentRestriction.hom
        (overHom q (k ≫ p) j (factorization_over q p i hi j k h))
        (@rankOpen Z U j (inferInstance : IsImmersion j)
          (forFactorization i j k h V) r) ⊤
          (rankOpen_le_preimage_top q (k ≫ p) j
            (factorization_over q p i hi j k h) (forFactorization i j k h V) r) ≫
      BivariantClass.ComponentRestriction.hom (overHom (k ≫ p) p k rfl)
        ⊤ ⊤ (by simp) =
      BivariantClass.ComponentRestriction.hom (overHom q p i hi)
        (@rankOpen Z X i h_i V r) ⊤
          (rankOpen_le_preimage_top q p i hi V r) := sorry

/-- Compose a completed closed-immersion class with the degree-zero flat-pullback class of
the open part of a closed-open factorization. -/
noncomputable def composeClasses
    {S Z U X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) (j : Z ⟶ U) (k : U ⟶ X)
    (h : j ≫ k = i) [h_i : IsImmersion i] [h_j : IsClosedImmersion j]
    [h_k : IsOpenImmersion k]
    (V : VirtualNormalBundle i)
    (closed : CompletedClass delta q (k ≫ p) j
      (factorization_over q p i hi j k h) (forFactorization i j k h V)) :
    CompletedClass delta q p i hi V :=
  fun r ↦ BivariantClass.Nonnegative.castHom delta
    (factorizationRestrictionHom_eq q p i hi j k h V r)
    (BivariantClass.Nonnegative.comp delta
      (BivariantClass.ComponentRestriction.hom
        (overHom q (k ≫ p) j (factorization_over q p i hi j k h))
        (@rankOpen Z U j (inferInstance : IsImmersion j)
          (forFactorization i j k h V) r) ⊤
          (rankOpen_le_preimage_top q (k ≫ p) j
            (factorization_over q p i hi j k h) (forFactorization i j k h V) r))
      (BivariantClass.ComponentRestriction.hom (overHom (k ≫ p) p k rfl)
        ⊤ ⊤ (by simp))
      (closed r)
      (BivariantClass.OpenRestriction.Completion.complete delta
        (overHom (k ≫ p) p k rfl) (fun _ : Unit ↦ ⊤) (fun _ : Unit ↦ ⊤)
        (fun _ ↦ Unit.unit) (fun _ ↦ by simp)
        (@DirectSum.of ℕ
          (fun n : ℕ ↦ BivariantClass delta (overHom (k ≫ p) p k rfl) (n : ℤ))
          (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
            (overHom (k ≫ p) p k rfl) (n : ℤ)).toAddCommMonoid)
          inferInstance 0
          (@BivariantClass.flatPullback _ _ delta _ _ _ _ _
            (overHom (k ≫ p) p k rfl) 0
            (by change Flat k; infer_instance)
            (Scheme.Hom.relativeDimension_zero_of_isOpenImmersion k)))
        Unit.unit))

/-- On a rank locus, `composeClasses` is the transported convolution of the closed class
with the completed degree-zero flat-pullback class. -/
theorem composeClasses_apply
    {S Z U X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) (j : Z ⟶ U) (k : U ⟶ X)
    (h : j ≫ k = i) [h_i : IsImmersion i] [h_j : IsClosedImmersion j]
    [h_k : IsOpenImmersion k] (V : VirtualNormalBundle i)
    (closed : CompletedClass delta q (k ≫ p) j
      (factorization_over q p i hi j k h) (forFactorization i j k h V)) (r : ℕ) :
    composeClasses delta q p i hi j k h V closed r =
      BivariantClass.Nonnegative.castHom delta
        (factorizationRestrictionHom_eq q p i hi j k h V r)
        (BivariantClass.Nonnegative.comp delta
          (BivariantClass.ComponentRestriction.hom
            (overHom q (k ≫ p) j (factorization_over q p i hi j k h))
            (@rankOpen Z U j (inferInstance : IsImmersion j)
              (forFactorization i j k h V) r) ⊤
            (rankOpen_le_preimage_top q (k ≫ p) j
              (factorization_over q p i hi j k h) (forFactorization i j k h V) r))
          (BivariantClass.ComponentRestriction.hom (overHom (k ≫ p) p k rfl)
            ⊤ ⊤ (by simp))
          (closed r)
          (BivariantClass.OpenRestriction.Completion.complete delta
            (overHom (k ≫ p) p k rfl) (fun _ : Unit ↦ ⊤) (fun _ : Unit ↦ ⊤)
            (fun _ ↦ Unit.unit) (fun _ ↦ by simp)
            (@DirectSum.of ℕ
              (fun n : ℕ ↦ BivariantClass delta (overHom (k ≫ p) p k rfl) (n : ℤ))
              (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
                (overHom (k ≫ p) p k rfl) (n : ℤ)).toAddCommMonoid)
              inferInstance 0
              (@BivariantClass.flatPullback _ _ delta _ _ _ _ _
                (overHom (k ≫ p) p k rfl) 0
                (by change Flat k; infer_instance)
                (Scheme.Hom.relativeDimension_zero_of_isOpenImmersion k)))
            Unit.unit)) := sorry

/-- A closed-immersion virtual-normal class operation assigns a completed class to every
closed immersion over the base scheme. -/
abbrev ClosedVirtualNormalClass
    (S : Scheme.{u}) [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] : Type (u + 1) :=
  {Z X : Scheme.{u}} → (q : Z ⟶ S) → (p : X ⟶ S) →
    [LocallyOfFiniteType q] → [LocallyOfFiniteType p] →
      (i : Z ⟶ X) → (hi : i ≫ p = q) → [IsClosedImmersion i] →
        (V : VirtualNormalBundle i) → CompletedClass delta q p i hi V

/-- A closed-immersion virtual-normal class operation respects enlargement of the ambient
scheme by an open immersion. -/
def RespectsOpenRestriction
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (closedClass : ClosedVirtualNormalClass S delta) : Prop :=
  ∀ {Z U X : Scheme.{u}} (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (j : Z ⟶ U) (k : U ⟶ X) [IsClosedImmersion j]
    [IsOpenImmersion k] [IsClosedImmersion (j ≫ k)]
    (hjk : (j ≫ k) ≫ p = q) (V : VirtualNormalBundle (j ≫ k)),
      composeClasses delta q p (j ≫ k) hjk j k rfl V
          (closedClass q (k ≫ p) j
            (factorization_over q p (j ≫ k) hjk j k rfl)
            (forFactorization (j ≫ k) j k rfl V)) =
        closedClass q p (j ≫ k) hjk V

/-- The completed bivariant class of a virtual normal bundle on an immersion, computed from
the canonical closed-open coborder factorization. -/
noncomputable def bivariantClass
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (closedClass : ClosedVirtualNormalClass S delta)
    (p : X ⟶ S) [LocallyOfFiniteType p] (i : Z ⟶ X) [IsImmersion i]
    (V : VirtualNormalBundle i) : CompletedClass delta (i ≫ p) p i rfl V :=
  composeClasses delta (i ≫ p) p i rfl i.liftCoborder i.coborderRange.ι
    i.liftCoborder_ι V
    (closedClass (i ≫ p) (i.coborderRange.ι ≫ p) i.liftCoborder
      (factorization_over (i ≫ p) p i rfl i.liftCoborder
        i.coborderRange.ι i.liftCoborder_ι) V.toCoborder)

/-- The class computed from the canonical coborder factorization agrees with the class
computed from every factorization as a closed immersion followed by an open immersion. -/
theorem bivariantClass_eq_ofFactorization
    {S Z U X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (closedClass : ClosedVirtualNormalClass S delta)
    (h_closed : RespectsOpenRestriction delta closedClass)
    (p : X ⟶ S) [LocallyOfFiniteType p] (i : Z ⟶ X) [IsImmersion i]
    (V : VirtualNormalBundle i) (j : Z ⟶ U) (k : U ⟶ X)
    [IsClosedImmersion j] [IsOpenImmersion k] (h : j ≫ k = i) :
    bivariantClass delta closedClass p i V =
      composeClasses delta (i ≫ p) p i rfl j k h V
        (closedClass (i ≫ p) (k ≫ p) j
          (factorization_over (i ≫ p) p i rfl j k h)
          (forFactorization i j k h V)) := sorry

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
