module

public import stacks_project.Chap42.«42_50_2_1_BivariantPushforward»
public import stacks_project.Chap42.Lemma_42_36_3
public import stacks_project.Chap42.Lemma_42_44_2_VectorBundleMap
public import stacks_project.Chap42.Lemma_42_48_1_GysinAtInfinity
public import stacks_project.Chap42.Lemma_42_48_2_BaseChange
public import stacks_project.Chap42.Lemma_42_54_1_Pullback
public import stacks_project.Chap42.Remark_42_54_11_Variant_for_immersions_Bivariant
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.NormalCone.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.FiniteLocallyFree

public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.ClosedImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- The deformation-to-the-normal-cone data with the traditional Chow-theoretic parameters. -/
abbrev ClosedSpecialization
    {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsClosedImmersion i]
    (V : VirtualNormalBundle i) : Type (u + 1) :=
  ClosedDeformation q p i hi V

namespace ClosedSpecialization

/-- The virtual-normal rank opens cover the source scheme. -/
theorem rankOpen_iSup {Z X : Scheme.{u}} (i : Z ⟶ X) [h_i : IsImmersion i]
    (V : VirtualNormalBundle i) :
    iSup (fun r : ℕ ↦ @rankOpen Z X i h_i V r) = ⊤ := by
  exact @Scheme.Modules.rankClopen_iSup Z V.module V.isFiniteLocallyFree

/-- Distinct virtual-normal rank opens are disjoint. -/
theorem rankOpen_pairwiseDisjoint {Z X : Scheme.{u}} (i : Z ⟶ X)
    [h_i : IsImmersion i] (V : VirtualNormalBundle i) :
    Pairwise (fun r s : ℕ ↦
      Disjoint (@rankOpen Z X i h_i V r : Set Z) (@rankOpen Z X i h_i V s : Set Z)) := by
  exact @Scheme.Modules.rankClopen_pairwiseDisjoint Z V.module V.isFiniteLocallyFree

/-- Every virtual-normal rank open is clopen. -/
theorem rankOpen_isClopen {Z X : Scheme.{u}} (i : Z ⟶ X) [h_i : IsImmersion i]
    (V : VirtualNormalBundle i) (r : ℕ) :
    IsClopen (@rankOpen Z X i h_i V r : Set Z) := by
  exact (@Scheme.Modules.rankClopen Z V.module V.isFiniteLocallyFree r).isClopen

/-- The one-element family of top opens covers its scheme. -/
theorem unitTop_iSup (X : Scheme.{u}) : iSup (fun _ : Unit ↦ (⊤ : X.Opens)) = ⊤ := by simp

/-- The one-element family of top opens is pairwise disjoint. -/
theorem unitTop_pairwiseDisjoint (X : Scheme.{u}) :
    Pairwise (fun _ _ : Unit ↦ Disjoint ((⊤ : X.Opens) : Set X) ((⊤ : X.Opens) : Set X)) := by
  intro a b h
  exact (h (Subsingleton.elim a b)).elim

/-- The top open of a scheme is clopen. -/
theorem unitTop_isClopen (X : Scheme.{u}) (_ : Unit) : IsClopen ((⊤ : X.Opens) : Set X) := isClopen_univ

end ClosedSpecialization


end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

open AlgebraicGeometry AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open scoped DirectSum

#check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.closedClass :
  ∀ {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V),
    BivariantClass.OpenRestriction.Completion delta (overHom q p i hi)
      (fun r : ℕ ↦ @rankOpen Z X i
        (inferInstance : IsImmersion i) V r)
      (fun _ : Unit ↦ ⊤) (fun _ ↦ Unit.unit)
      (fun r ↦ rankOpen_le_preimage_top q p i hi V r))
#check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.closedClass_pullback :
  ∀ {S Z X Z' X' : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    (q' : Z' ⟶ S) (p' : X' ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    [LocallyOfFiniteType q'] [LocallyOfFiniteType p']
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (i' : Z' ⟶ X') (hi' : i' ≫ p' = q') [h_i' : IsClosedImmersion i']
    (g : Over.mk q' ⟶ Over.mk q) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left)
    (V : VirtualNormalBundle i)
    (D : ClosedDeformation q p i hi V)
    (D' : ClosedDeformation q' p' i' hi'
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V)),
    closedClass delta q' p' i' hi'
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) D' =
      closedClassBaseChange delta q p q' p' i hi i' hi' g f square V D)
#check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.closedClass_eq_completeOfRank :
  ∀ {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r V.module],
    closedClass delta q p i hi V D =
      BivariantClass.OpenRestriction.Completion.complete delta
        (overHom q p i hi)
        (fun n : ℕ ↦ @rankOpen Z X i
          (inferInstance : IsImmersion i) V n)
        (fun _ : Unit ↦ ⊤) (fun _ ↦ Unit.unit)
        (fun n ↦ rankOpen_le_preimage_top q p i hi V n)
        (@DirectSum.of ℕ
          (fun n : ℕ ↦ BivariantClass delta (overHom q p i hi) (n : ℤ))
          (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
            (overHom q p i hi) (n : ℤ)).toAddCommMonoid)
          inferInstance r (globalClassOfRank delta q p i hi V D r)))
