module

public import Mathlib.RingTheory.Binomial
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberEulerCharacteristic
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.EnvelopeDescent
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.RankDecomposition
public import ReasLib.AlgebraicGeometry.BivariantClass.ComponentRestriction.CapTransport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberEulerCharacteristic.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Characterization

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
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
    BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk π))
        (rankClopen E hPerfect z).toOpens (rankClopen E hPerfect z).toOpens
        (rankClopen_le_identity_preimage π E hPerfect z) =
      𝟙 (BivariantClass.ComponentRestriction.over (Over.mk π)
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
            (BivariantClass.ComponentRestriction.over (Over.mk π)
              (rankClopen E hPerfect z).toOpens).hom)
          0
          (ChowCohomology.Nonnegative.intCast δ
            (BivariantClass.ComponentRestriction.over (Over.mk π)
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
          (BivariantClass.ComponentRestriction.over (Over.mk π)
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
          (BivariantClass.ComponentRestriction.over (Over.mk π)
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
          (BivariantClass.ComponentRestriction.over (Over.mk π)
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

private theorem fiberEulerChar_eq_zero_of_isZero {T : Scheme.{u}}
    (F : RingedSpace.ModuleDerived T.toRingedSpace) (hF : IsZero F) (t : T) :
    Scheme.ModuleDerived.fiberEulerChar F t = 0 := by
  rw [Scheme.ModuleDerived.fiberEulerChar_apply]
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  have hs := (RingedSpace.ModuleDerived.Stalk.functor t).map_isZero hF
  have hz : IsZero (DerivedCategory.ResidueField.homology (T.presheaf.stalk t)
      (RingedSpace.ModuleDerived.Stalk.obj F t) j) := by
    apply (DerivedCategory.homologyFunctor _ j).map_isZero
    exact (ModuleCat.derivedExtensionOfScalars
      (algebraMap (T.presheaf.stalk t) (IsLocalRing.ResidueField (T.presheaf.stalk t)))).map_isZero hs
  -- Local instance justification (proof-local temporary data): the zero residue-field homology module is subsingleton, as required to compute its finrank as zero.
  letI := ModuleCat.subsingleton_of_isZero hz
  simp [Module.finrank_zero_of_subsingleton]

private theorem zero_class_transport
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (A : Over S) [LocallyOfFiniteType A.hom] (a : A ⟶ A) (e : a = 𝟙 A) :
    e.symm ▸ (0 : ChowCohomology.Nonnegative.degree δ A.hom 0) =
      BivariantClass.pointwiseZero δ a 0 := by
  subst a
  rfl

/-- A positive binomial virtual-rank class acts trivially on a test square
whose target has zero derived pullback of the perfect complex. -/
theorem rankChoose_cap_eq_zero_of_isZero_pullback
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (n : ℕ) (hn : 0 < n)
    {A B : Over S} [LocallyOfFiniteType A.hom] [LocallyOfFiniteType B.hom]
    (i : A ⟶ Over.mk π) (f' : A ⟶ B) (g : B ⟶ Over.mk π)
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (𝟙 (Over.mk π) : Over.mk π ⟶ Over.mk π).left g.left)
    (hZero : IsZero ((RingedSpace.modulePullbackDerived g.left.toShHom).obj E))
    (k : ℤ) : (rankChoose δ π E hPerfect n).cap i f' g square k = 0 := by
  let U : (Over.mk π).left.Opens := (rankClopen E hPerfect 0).toOpens
  have range_g : Set.range g.left ⊆ Set.range U.ι := by
    rintro x ⟨b, rfl⟩
    refine ⟨⟨g.left b, ?_⟩, rfl⟩
    change virtualRank E hPerfect (g.left b) = 0
    rw [virtualRank_apply]
    have hbase := congrFun (Scheme.ModuleDerived.fiberEulerChar_pullback g.left E
      hPerfect.isPseudoCoherent) b
    exact hbase.symm.trans (fiberEulerChar_eq_zero_of_isZero _ hZero b)
  let lift := IsOpenImmersion.lift U.ι g.left range_g
  have lift_fac : lift ≫ U.ι = g.left := IsOpenImmersion.lift_fac _ _ _
  let gU : B ⟶ BivariantClass.ComponentRestriction.over (Over.mk π) U :=
    Over.homMk lift (by
      change lift ≫ (U.ι ≫ π) = B.hom
      rw [← Category.assoc, lift_fac]
      exact g.w)
  have hg : gU ≫ BivariantClass.ComponentRestriction.ι (Over.mk π) U = g := by
    apply Over.OverMorphism.ext
    exact lift_fac
  -- Local instance justification (proof-local temporary data): the constructed factor through the rank-zero open inherits finite type from g, which component cap evaluation requires.
  letI : LocallyOfFiniteType gU.left := by
    exact @locallyOfFiniteType_of_comp _ _ _ gU.left U.ι (by
      change LocallyOfFiniteType (lift ≫ U.ι)
      rw [lift_fac]
      infer_instance)
  have hi : (f' ≫ gU) ≫ BivariantClass.ComponentRestriction.ι (Over.mk π) U = i := by
    rw [Category.assoc, hg]
    apply Over.OverMorphism.ext
    simpa only [Over.comp_left, Over.id_left, Category.comp_id] using square.w.symm
  have ambient : IsPullback
      ((f' ≫ gU) ≫ BivariantClass.ComponentRestriction.ι (Over.mk π) U).left
      f'.left (𝟙 (Over.mk π) : Over.mk π ⟶ Over.mk π).left
      (gU ≫ BivariantClass.ComponentRestriction.ι (Over.mk π) U).left := by
    simpa only [hi, hg] using square
  have component : IsPullback (f' ≫ gU).left f'.left
      (BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk π)) U U
        (rankClopen_le_identity_preimage π E hPerfect 0)).left gU.left := by
    rw [rankClopen_identity_restriction]
    apply IsPullback.of_right ambient _ (IsPullback.of_id_snd : IsPullback
      (BivariantClass.ComponentRestriction.ι (Over.mk π) U).left
      (𝟙 (BivariantClass.ComponentRestriction.over (Over.mk π) U) :
        BivariantClass.ComponentRestriction.over (Over.mk π) U ⟶ _).left
      (𝟙 (Over.mk π) : Over.mk π ⟶ Over.mk π).left
      (BivariantClass.ComponentRestriction.ι (Over.mk π) U).left)
    simp only [Over.comp_left, Category.comp_id]
  have hc := rankChoose_component δ π E hPerfect n 0
  change BivariantClass.ComponentRestriction.restrict δ (𝟙 (Over.mk π)) 0 U U
      (rankClopen_le_identity_preimage π E hPerfect 0) (rankChoose δ π E hPerfect n) = _ at hc
  rw [Ring.choose_zero_pos ℤ hn] at hc
  simp only [ChowCohomology.Nonnegative.intCast, zero_zsmul] at hc
  have hc0 := hc.trans (zero_class_transport δ
    (BivariantClass.ComponentRestriction.over (Over.mk π) U) _
    (rankClopen_identity_restriction π E hPerfect 0))
  have comparison := BivariantClass.ComponentRestriction.restrict_cap_of_isPullback
    δ (𝟙 (Over.mk π)) 0 U U (rankClopen_le_identity_preimage π E hPerfect 0)
    (rankChoose δ π E hPerfect n) (f' ≫ gU) f' gU component ambient k
  rw [hc0] at comparison
  simpa only [hi, hg, BivariantClass.pointwiseZero] using comparison.symm

end AlgebraicGeometry.ChernClass.Derived

