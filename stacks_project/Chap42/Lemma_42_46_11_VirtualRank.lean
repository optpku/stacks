module

public import Mathlib.RingTheory.Binomial
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberEulerCharacteristic
public import stacks_project.Chap42.Definition_42_46_3_DerivedChern
public import stacks_project.Chap42.Remark_42_38_10_ChernClass

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Derived

/-- The locally constant virtual rank of a perfect derived module, given by the Euler
characteristic of its derived fibers. -/
noncomputable def virtualRank {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) : LocallyConstant X ℤ :=
  ⟨Scheme.ModuleDerived.fiberEulerChar E,
    Scheme.ModuleDerived.fiberEulerChar_isLocallyConstant E hPerfect⟩

/-- The virtual rank evaluates to the Euler characteristic of the derived fiber. -/
theorem virtualRank_apply {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (x : X) :
    virtualRank E hPerfect x = Scheme.ModuleDerived.fiberEulerChar E x := sorry

/-- Isomorphic perfect derived modules have the same locally constant virtual rank. -/
theorem virtualRank_eq_of_iso {X : Scheme.{u}}
    {E F : RingedSpace.ModuleDerived X.toRingedSpace} (e : E ≅ F)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F) :
    virtualRank E hEPerfect = virtualRank F hFPerfect := sorry

/-- The clopen locus on which a perfect derived module has virtual rank `z`. -/
noncomputable def rankClopen {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (z : ℤ) : Clopens X :=
  ⟨{x : X | virtualRank E hPerfect x = z},
    (virtualRank E hPerfect).isLocallyConstant.isClopen_fiber z⟩

/-- Membership in the virtual-rank locus is equality with the indicated integer. -/
theorem mem_rankClopen {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (z : ℤ) (x : X) :
    x ∈ rankClopen E hPerfect z ↔ virtualRank E hPerfect x = z := sorry

/-- The virtual-rank loci cover the underlying scheme. -/
theorem rankClopen_iSup {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) :
    iSup (fun z : ℤ ↦ (rankClopen E hPerfect z).toOpens) = ⊤ := sorry

/-- Distinct virtual-rank loci are disjoint. -/
theorem rankClopen_pairwiseDisjoint {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) :
    Pairwise (fun z w : ℤ ↦
      Disjoint (rankClopen E hPerfect z : Set X) (rankClopen E hPerfect w : Set X)) := sorry

/-- Each virtual-rank open is preserved by the identity morphism of `Over.mk π`. -/
theorem rankClopen_le_identity_preimage
    {S X : Scheme.{u}} (π : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (z : ℤ) :
    (rankClopen E hPerfect z).toOpens ≤
      (𝟙 (Over.mk π) : Over.mk π ⟶ Over.mk π).left ⁻¹ᵁ
        (rankClopen E hPerfect z).toOpens := sorry

/-- Restricting the identity of `Over.mk π` to a virtual-rank locus gives the identity
of that open component. -/
theorem rankClopen_identity_restriction
    {S X : Scheme.{u}} (π : X ⟶ S)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (z : ℤ) :
    BivariantClass.OpenRestriction.hom (𝟙 (Over.mk π))
        (rankClopen E hPerfect z).toOpens (rankClopen E hPerfect z).toOpens
        (rankClopen_le_identity_preimage π E hPerfect z) =
      𝟙 (BivariantClass.OpenRestriction.over (Over.mk π)
        (rankClopen E hPerfect z).toOpens) := sorry

/-- Glue an integer-valued function of virtual rank into a degree-zero Chow class. -/
noncomputable def rankValueClass
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (g : ℤ → ℤ) :
    ChowCohomology.Nonnegative.degree δ π 0 :=
  ((BivariantClass.OpenRestriction.Completion.globalEquiv δ (𝟙 (Over.mk π))
      (fun z : ℤ ↦ (rankClopen E hPerfect z).toOpens)
      (fun z : ℤ ↦ (rankClopen E hPerfect z).toOpens) id
      (rankClopen_iSup E hPerfect) (rankClopen_iSup E hPerfect)
      (rankClopen_pairwiseDisjoint E hPerfect)
      (rankClopen_pairwiseDisjoint E hPerfect)
      (fun z ↦ (rankClopen E hPerfect z).isClopen)
      (fun z ↦ (rankClopen E hPerfect z).isClopen)
      (rankClopen_le_identity_preimage π E hPerfect))
    (Eq.mp
      (ChowCohomology.completedRing_eq_completion δ (Over.mk π)
        (fun z : ℤ ↦ (rankClopen E hPerfect z).toOpens)
        (rankClopen_iSup E hPerfect) (rankClopen_pairwiseDisjoint E hPerfect)
        (fun z ↦ (rankClopen E hPerfect z).isClopen)
        (rankClopen_le_identity_preimage π E hPerfect))
      ((fun z : ℤ ↦ DirectSum.of
          (ChowCohomology.Nonnegative.degree δ
            (BivariantClass.OpenRestriction.over (Over.mk π)
              (rankClopen E hPerfect z).toOpens).hom)
          0
          (ChowCohomology.Nonnegative.intCast δ
            (BivariantClass.OpenRestriction.over (Over.mk π)
              (rankClopen E hPerfect z).toOpens).hom (g z))) :
        ChowCohomology.completedRing δ (Over.mk π)
          (fun z : ℤ ↦ (rankClopen E hPerfect z).toOpens)
          (rankClopen_iSup E hPerfect) (rankClopen_pairwiseDisjoint E hPerfect)
          (fun z ↦ (rankClopen E hPerfect z).isClopen)
          (rankClopen_le_identity_preimage π E hPerfect)))).1 0

/-- On the virtual-rank-`z` component, `rankValueClass` is the degree-zero integer
cast of `g z`. -/
theorem rankValueClass_component
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (g : ℤ → ℤ) (z : ℤ) :
    (BivariantClass.OpenRestriction.Completion.componentsEquiv δ (𝟙 (Over.mk π)) 0
      (fun w : ℤ ↦ (rankClopen E hPerfect w).toOpens)
      (fun w : ℤ ↦ (rankClopen E hPerfect w).toOpens) id
      (rankClopen_iSup E hPerfect) (rankClopen_iSup E hPerfect)
      (rankClopen_pairwiseDisjoint E hPerfect)
      (rankClopen_pairwiseDisjoint E hPerfect)
      (fun w ↦ (rankClopen E hPerfect w).isClopen)
      (fun w ↦ (rankClopen E hPerfect w).isClopen)
      (rankClopen_le_identity_preimage π E hPerfect))
        (rankValueClass δ π E hPerfect g) z =
      (rankClopen_identity_restriction π E hPerfect z).symm ▸
        ChowCohomology.Nonnegative.intCast δ
          (BivariantClass.OpenRestriction.over (Over.mk π)
            (rankClopen E hPerfect z).toOpens).hom (g z) := sorry

/-- The degree-zero Chow class represented by the virtual rank. -/
noncomputable def rankClass
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) :
    ChowCohomology.Nonnegative.degree δ π 0 :=
  rankValueClass δ π E hPerfect id

/-- On the virtual-rank-`z` component, `rankClass` is the degree-zero integer cast of `z`. -/
theorem rankClass_component
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (z : ℤ) :
    (BivariantClass.OpenRestriction.Completion.componentsEquiv δ (𝟙 (Over.mk π)) 0
      (fun w : ℤ ↦ (rankClopen E hPerfect w).toOpens)
      (fun w : ℤ ↦ (rankClopen E hPerfect w).toOpens) id
      (rankClopen_iSup E hPerfect) (rankClopen_iSup E hPerfect)
      (rankClopen_pairwiseDisjoint E hPerfect)
      (rankClopen_pairwiseDisjoint E hPerfect)
      (fun w ↦ (rankClopen E hPerfect w).isClopen)
      (fun w ↦ (rankClopen E hPerfect w).isClopen)
      (rankClopen_le_identity_preimage π E hPerfect))
        (rankClass δ π E hPerfect) z =
      (rankClopen_identity_restriction π E hPerfect z).symm ▸
        ChowCohomology.Nonnegative.intCast δ
          (BivariantClass.OpenRestriction.over (Over.mk π)
            (rankClopen E hPerfect z).toOpens).hom z := sorry

/-- The degree-zero Chow class represented by the generalized binomial coefficient of
the virtual rank. -/
noncomputable def rankChoose
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (n : ℕ) :
    ChowCohomology.Nonnegative.degree δ π 0 :=
  rankValueClass δ π E hPerfect (fun z : ℤ ↦ Ring.choose z n)

/-- On the virtual-rank-`z` component, `rankChoose n` is the degree-zero cast of
`Ring.choose z n`. -/
theorem rankChoose_component
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (n : ℕ) (z : ℤ) :
    (BivariantClass.OpenRestriction.Completion.componentsEquiv δ (𝟙 (Over.mk π)) 0
      (fun w : ℤ ↦ (rankClopen E hPerfect w).toOpens)
      (fun w : ℤ ↦ (rankClopen E hPerfect w).toOpens) id
      (rankClopen_iSup E hPerfect) (rankClopen_iSup E hPerfect)
      (rankClopen_pairwiseDisjoint E hPerfect)
      (rankClopen_pairwiseDisjoint E hPerfect)
      (fun w ↦ (rankClopen E hPerfect w).isClopen)
      (fun w ↦ (rankClopen E hPerfect w).isClopen)
      (rankClopen_le_identity_preimage π E hPerfect))
        (rankChoose δ π E hPerfect n) z =
      (rankClopen_identity_restriction π E hPerfect z).symm ▸
        ChowCohomology.Nonnegative.intCast δ
          (BivariantClass.OpenRestriction.over (Over.mk π)
            (rankClopen E hPerfect z).toOpens).hom (Ring.choose z n) := sorry

/-- Virtual-rank Chow classes are invariant under isomorphism of perfect derived modules. -/
theorem rankClass_eq_of_iso
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    {E F : RingedSpace.ModuleDerived X.toRingedSpace} (e : E ≅ F)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F) :
    rankClass δ π E hEPerfect = rankClass δ π F hFPerfect := sorry

/-- Generalized binomial virtual-rank classes are invariant under isomorphism. -/
theorem rankChoose_eq_of_iso
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    {E F : RingedSpace.ModuleDerived X.toRingedSpace} (e : E ≅ F)
    (hEPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hFPerfect : RingedSpace.ModuleDerived.IsPerfect F) (n : ℕ) :
    rankChoose δ π E hEPerfect n = rankChoose δ π F hFPerfect n := sorry

/-- The virtual-rank class is the degree-zero Newton class. -/
theorem rankClass_eq_newtonClass_zero
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    rankClass δ π E hPerfect = newtonClass δ π classes E hPerfect hDefined 0 := sorry

end AlgebraicGeometry.ChernClass.Derived
