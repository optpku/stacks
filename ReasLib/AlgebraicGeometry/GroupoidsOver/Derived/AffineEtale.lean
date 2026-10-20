module

public import ReasLib.AlgebraicGeometry.RingedSite.CommRing
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Affine
public import ReasLib.CategoryTheory.Adjunction.Restriction.InverseImage
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Closure
public import ReasLib.CategoryTheory.Fibered.InheritedTopology
public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Topology
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.QuasiCoherent
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.TensorSections
public import ReasLib.Algebra.Homology.CochainComplex.KFlat

/-!
# Affine étale comparison of the chaotic affine site

The identity-on-objects morphism of ringed sites
`ε : 𝒳_affine,étale ⟶ 𝒳_affine` from the inherited affine étale topology to
the chaotic topology on `𝒳_affine`, together with the derived adjunction
`ε^* ⊣ Rε_*`, its K-flat slice-sections comparison, and the resulting
equivalences on quasi-coherent derived objects.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open CategoryTheory.ModulesOnCategory
open RingedSite RingedSite.Hom

noncomputable section

universe u w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- The Grothendieck topology on `𝒳_affine` inherited from `(Aff/S)_étale`. -/
abbrev affineSiteEtaleTopology : GrothendieckTopology (affineSite X) :=
  (affineSiteToAffineOver X).inheritedTopology
    (StandardTopology.Affine.topology StandardTopology.etale S)

/-- `affineSiteEtaleTopology X` is the topology inherited along
`affineSiteToAffineOver X` from `(Aff/S)_étale`. -/
theorem affineSiteEtaleTopology_eq :
    affineSiteEtaleTopology X =
      (affineSiteToAffineOver X).inheritedTopology
        (StandardTopology.Affine.topology StandardTopology.etale S) :=
  rfl

/-- The chaotic topology is coarser than the inherited affine étale topology. -/
theorem chaotic_le_affineSiteEtale :
    (⊥ : GrothendieckTopology (affineSite X)) ≤ affineSiteEtaleTopology X :=
  bot_le

/-- A represented family covers in the inherited affine étale topology if and
only if its image under `affineSiteToAffineOver` covers in `(Aff/S)_étale`. -/
theorem ofArrows_mem_affineSiteEtaleTopology_iff {x : affineSite X} {ι : Type w}
    (Y : ι → affineSite X) (f : ∀ i, Y i ⟶ x) :
    Sieve.generate (Presieve.ofArrows Y f) ∈ affineSiteEtaleTopology X x ↔
      Sieve.generate
          (Presieve.ofArrows (fun i ↦ (affineSiteToAffineOver X).obj (Y i))
            (fun i ↦ (affineSiteToAffineOver X).map (f i))) ∈
        StandardTopology.Affine.topology StandardTopology.etale S
          ((affineSiteToAffineOver X).obj x) :=
  sorry

/-- The identity functor is continuous from the chaotic topology to the
inherited affine étale topology. -/
instance instIdIsContinuousChaoticEtale :
    (𝟭 (affineSite X)).IsContinuous ⊥ (affineSiteEtaleTopology X) :=
  Functor.id_isContinuous_of_le (chaotic_le_affineSiteEtale X)

/-- The identity functor is a morphism of sites from the chaotic affine site to
the inherited affine étale site. -/
instance instIdIsMorphismOfSitesChaoticEtale :
    IsMorphismOfSites ⊥ (affineSiteEtaleTopology X) (𝟭 (affineSite X)) :=
  IsMorphismOfSites.id_of_le (chaotic_le_affineSiteEtale X)

/-- Composition with `CommRingCat ⥤ RingCat` preserves sheaves for the inherited
affine étale topology. -/
instance instAffineSiteEtaleHasSheafCompose :
    (affineSiteEtaleTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  sorry

variable [HasWeakSheafify (affineSiteEtaleTopology X) CommRingCat.{u + 1}]
variable [∀ P : (affineSite X)ᵒᵖ ⥤ CommRingCat.{u + 1},
    (𝟭 (affineSite X)).op.HasLeftKanExtension P]

/-- The inverse-image commutative structure sheaf of `𝒪` on `𝒳_affine,étale`. -/
abbrev affineEtaleStructureSheaf :
    Sheaf (affineSiteEtaleTopology X) CommRingCat.{u + 1} :=
  ((𝟭 (affineSite X)).sheafPullback CommRingCat.{u + 1} ⊥
      (affineSiteEtaleTopology X)).obj (affineStructureSheaf X)

/-- `affineEtaleStructureSheaf X` is identity inverse image of the chaotic
structure sheaf along `⊥ ≤ 𝒳_affine,étale`. -/
theorem affineEtaleStructureSheaf_eq :
    affineEtaleStructureSheaf X =
      ((𝟭 (affineSite X)).sheafPullback CommRingCat.{u + 1} ⊥
          (affineSiteEtaleTopology X)).obj (affineStructureSheaf X) :=
  rfl

/-- The identity-on-objects comparison morphism of ringed sites
`ε : 𝒳_affine,étale ⟶ 𝒳_affine`. -/
def affineEtaleComparison :
    Hom
      (ofCommRingSheaf (affineSiteEtaleTopology X) (affineEtaleStructureSheaf X))
      (ofCommRingSheaf ⊥ (affineStructureSheaf X)) :=
  ofPullback (JC := affineSiteEtaleTopology X) (JD := ⊥)
    (𝟭 (affineSite X)) (affineStructureSheaf X)

/-- The base of `affineEtaleComparison X` is the identity functor. -/
theorem affineEtaleComparison_base :
    (affineEtaleComparison X).base = 𝟭 (affineSite X) :=
  rfl

/-- Module pushforward along `ε` is a right adjoint. -/
instance instAffineEtaleComparison_modulePushforwardIsRightAdjoint :
    ((affineEtaleComparison X).modulePushforward.{u + 1}).IsRightAdjoint :=
  sorry

variable [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u + 1} (affineEtaleComparison X))
    (ModuleQis.{u + 1}
      (ofCommRingSheaf (affineSiteEtaleTopology X) (affineEtaleStructureSheaf X)))]
variable [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u + 1} (affineEtaleComparison X))
    (ModuleQis.{u + 1} (ofCommRingSheaf ⊥ (affineStructureSheaf X)))]

/-- The total-derived pair condition for `ε^* ⊣ Rε_*`. -/
instance instAffineEtaleComparison_hasPair :
    DerivedAdjunction.HasPair.{u + 1} (affineEtaleComparison X) :=
  sorry

/-- The derived adjunction `ε^* ⊣ Rε_*` of the affine étale comparison. -/
def affineEtaleDerivedAdjunction :
    modulePullbackDerived.{u + 1} (affineEtaleComparison X) ⊣
      modulePushforwardDerived.{u + 1} (affineEtaleComparison X) :=
  moduleDerivedAdjunction.{u + 1} (affineEtaleComparison X)

/-- `affineEtaleDerivedAdjunction X` is the canonical derived adjunction of
`affineEtaleComparison X`. -/
theorem affineEtaleDerivedAdjunction_eq :
    affineEtaleDerivedAdjunction X =
      moduleDerivedAdjunction.{u + 1} (affineEtaleComparison X) :=
  rfl

/-- Derived pushforward along `ε` is full. -/
instance instAffineEtaleComparison_pushforwardDerivedFull :
    (modulePushforwardDerived.{u + 1} (affineEtaleComparison X)).Full :=
  sorry

/-- Derived pushforward along `ε` is faithful. -/
instance instAffineEtaleComparison_pushforwardDerivedFaithful :
    (modulePushforwardDerived.{u + 1} (affineEtaleComparison X)).Faithful :=
  sorry

/-- The object property of derived modules on `𝒳_affine,étale` whose derived
pushforward along `ε` is quasi-coherent on the chaotic affine site. -/
abbrev affineEtaleTargetProperty : ObjectProperty
    (ModuleDerived.{u + 1}
      (ofCommRingSheaf (affineSiteEtaleTopology X) (affineEtaleStructureSheaf X))) :=
  (qcProperty X).inverseImage
    (modulePushforwardDerived.{u + 1} (affineEtaleComparison X))

/-- A derived module satisfies `affineEtaleTargetProperty X` if and only if its
derived pushforward along `ε` lies in `qcProperty X`. -/
theorem affineEtaleTargetProperty_mem_iff
    (K : ModuleDerived.{u + 1}
      (ofCommRingSheaf (affineSiteEtaleTopology X) (affineEtaleStructureSheaf X))) :
    affineEtaleTargetProperty X K ↔
      qcProperty X
        ((modulePushforwardDerived.{u + 1} (affineEtaleComparison X)).obj K) :=
  Iff.rfl


/-- The canonical tensor-sheafification comparison to derived sections on every affine
étale slice is invertible for every K-flat coefficient complex over the original section ring. -/
theorem affineEtaleComparison_kFlatSections_isIso
    (x : affineSite X)
    (M : CochainComplex (_root_.ModuleCat ((affineStructureSheaf X).obj.obj (Opposite.op x))) ℤ)
    (hM : M.IsKFlat) :
    IsIso (TensorSections.comparison (affineStructureSheaf X).obj x
      (affineSiteEtaleTopology X) (affineEtaleStructureSheaf X)
      (((𝟭 (affineSite X)).sheafAdjunctionContinuous CommRingCat.{u + 1} ⊥
        (affineSiteEtaleTopology X)).unit.app (affineStructureSheaf X)).hom M) := sorry

/-- The derived unit of the affine étale comparison is invertible on quasi-coherent objects. -/
theorem affineEtaleComparison_unitCondition :
    qcProperty X ≤ (affineEtaleDerivedAdjunction X).unitIsoProperty :=
  sorry

/-- Derived pushforward restricts to an equivalence onto quasi-coherent derived objects. -/
instance affineEtaleComparison_pushforwardRestriction_isEquivalence :
    (Adjunction.InverseImageRestriction.right (qcProperty X) :
        (affineEtaleTargetProperty X).FullSubcategory ⥤
          (qcProperty X).FullSubcategory).IsEquivalence :=
  Adjunction.InverseImageRestriction.right_isEquivalence
    (affineEtaleDerivedAdjunction X) (qcProperty X) (affineEtaleComparison_unitCondition X)

/-- Derived pullback restricts to the inverse equivalence on quasi-coherent derived objects. -/
instance affineEtaleComparison_pullbackRestriction_isEquivalence :
    (Adjunction.InverseImageRestriction.left (affineEtaleDerivedAdjunction X)
      (qcProperty X) (affineEtaleComparison_unitCondition X)).IsEquivalence :=
  Adjunction.InverseImageRestriction.left_isEquivalence
    (affineEtaleDerivedAdjunction X) (qcProperty X) (affineEtaleComparison_unitCondition X)

/-- The affine étale comparison has the K-flat slice-sections property, its derived unit
is invertible on quasi-coherent objects, and its restricted adjoint functors are equivalences. -/
theorem affineEtaleComparison_spec :
    (∀ (x : affineSite X)
      (M : CochainComplex (_root_.ModuleCat ((affineStructureSheaf X).obj.obj (Opposite.op x))) ℤ),
      M.IsKFlat → IsIso (TensorSections.comparison (affineStructureSheaf X).obj x
        (affineSiteEtaleTopology X) (affineEtaleStructureSheaf X)
        (((𝟭 (affineSite X)).sheafAdjunctionContinuous CommRingCat.{u + 1} ⊥
        (affineSiteEtaleTopology X)).unit.app (affineStructureSheaf X)).hom M)) ∧
    (qcProperty X ≤ (affineEtaleDerivedAdjunction X).unitIsoProperty) ∧
    (Adjunction.InverseImageRestriction.right (qcProperty X) :
      (affineEtaleTargetProperty X).FullSubcategory ⥤
        (qcProperty X).FullSubcategory).IsEquivalence ∧
    (Adjunction.InverseImageRestriction.left (affineEtaleDerivedAdjunction X)
      (qcProperty X) (affineEtaleComparison_unitCondition X)).IsEquivalence :=
  ⟨affineEtaleComparison_kFlatSections_isIso X,
    affineEtaleComparison_unitCondition X,
    affineEtaleComparison_pushforwardRestriction_isEquivalence X,
    affineEtaleComparison_pullbackRestriction_isEquivalence X⟩

end AlgebraicGeometry.GroupoidsOver
