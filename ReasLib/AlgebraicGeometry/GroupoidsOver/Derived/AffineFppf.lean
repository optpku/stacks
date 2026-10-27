/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
public import ReasLib.CategoryTheory.Functor.KanExtension.Identity
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Affine fppf comparison of the chaotic affine site

The identity-on-objects morphism of ringed sites
`ε : 𝒳_affine,fppf ⟶ 𝒳_affine` from the inherited affine fppf topology to
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

/-- The Grothendieck topology on `𝒳_affine` inherited from `(Aff/S)_fppf`. -/
abbrev affineSiteFppfTopology : GrothendieckTopology (affineSite X) :=
  (affineSiteToAffineOver X).inheritedTopology
    (StandardTopology.Affine.topology StandardTopology.fppf S)

/-- `affineSiteFppfTopology X` is the topology inherited along
`affineSiteToAffineOver X` from `(Aff/S)_fppf`. -/
theorem affineSiteFppfTopology_eq :
    affineSiteFppfTopology X =
      (affineSiteToAffineOver X).inheritedTopology
        (StandardTopology.Affine.topology StandardTopology.fppf S) :=
  rfl

/-- The chaotic topology is coarser than the inherited affine fppf topology. -/
theorem chaotic_le_affineSiteFppf :
    (⊥ : GrothendieckTopology (affineSite X)) ≤ affineSiteFppfTopology X :=
  bot_le

/-- A represented family covers in the inherited affine fppf topology if and
only if its image under `affineSiteToAffineOver` covers in `(Aff/S)_fppf`. -/
theorem ofArrows_mem_affineSiteFppfTopology_iff {x : affineSite X} {ι : Type w}
    (Y : ι → affineSite X) (f : ∀ i, Y i ⟶ x) :
    Sieve.generate (Presieve.ofArrows Y f) ∈ affineSiteFppfTopology X x ↔
      Sieve.generate
          (Presieve.ofArrows (fun i ↦ (affineSiteToAffineOver X).obj (Y i))
            (fun i ↦ (affineSiteToAffineOver X).map (f i))) ∈
        StandardTopology.Affine.topology StandardTopology.fppf S
          ((affineSiteToAffineOver X).obj x) :=
  sorry

/-- The identity functor is continuous from the chaotic topology to the
inherited affine fppf topology. -/
instance instIdIsContinuousChaoticFppf :
    (𝟭 (affineSite X)).IsContinuous ⊥ (affineSiteFppfTopology X) :=
  Functor.id_isContinuous_of_le (chaotic_le_affineSiteFppf X)

/-- The identity functor is a morphism of sites from the chaotic affine site to
the inherited affine fppf site. -/
instance instIdIsMorphismOfSitesChaoticFppf :
    IsMorphismOfSites ⊥ (affineSiteFppfTopology X) (𝟭 (affineSite X)) :=
  IsMorphismOfSites.id_of_le (chaotic_le_affineSiteFppf X)

/-- The inverse-image commutative structure sheaf of `𝒪` on `𝒳_affine,fppf`. -/
abbrev affineFppfStructureSheaf :
    Sheaf (affineSiteFppfTopology X) CommRingCat.{u + 1} :=
  ((𝟭 (affineSite X)).sheafPullback CommRingCat.{u + 1} ⊥
      (affineSiteFppfTopology X)).obj (affineStructureSheaf X)

/-- `affineFppfStructureSheaf X` is identity inverse image of the chaotic
structure sheaf along `⊥ ≤ 𝒳_affine,fppf`. -/
theorem affineFppfStructureSheaf_eq :
    affineFppfStructureSheaf X =
      ((𝟭 (affineSite X)).sheafPullback CommRingCat.{u + 1} ⊥
          (affineSiteFppfTopology X)).obj (affineStructureSheaf X) :=
  rfl

/-- The identity-on-objects comparison morphism of ringed sites
`ε : 𝒳_affine,fppf ⟶ 𝒳_affine`. -/
def affineFppfComparison :
    Hom
      (ofCommRingSheaf (affineSiteFppfTopology X) (affineFppfStructureSheaf X))
      (ofCommRingSheaf ⊥ (affineStructureSheaf X)) :=
  ofPullback (JC := affineSiteFppfTopology X) (JD := ⊥)
    (𝟭 (affineSite X)) (affineStructureSheaf X)

/-- The base of `affineFppfComparison X` is the identity functor. -/
theorem affineFppfComparison_base :
    (affineFppfComparison X).base = 𝟭 (affineSite X) :=
  rfl

/-- Module pushforward along `ε` is a right adjoint. -/
instance instAffineFppfComparison_modulePushforwardIsRightAdjoint :
    ((affineFppfComparison X).modulePushforward.{u + 1}).IsRightAdjoint :=
  sorry

variable [Functor.HasRightDerivedFunctor
    (modulePushforwardToDerived.{u + 1} (affineFppfComparison X))
    (ModuleQis.{u + 1}
      (ofCommRingSheaf (affineSiteFppfTopology X) (affineFppfStructureSheaf X)))]
variable [Functor.HasLeftDerivedFunctor
    (modulePullbackToDerived.{u + 1} (affineFppfComparison X))
    (ModuleQis.{u + 1} (ofCommRingSheaf ⊥ (affineStructureSheaf X)))]

/-- The total-derived pair condition for `ε^* ⊣ Rε_*`. -/
instance instAffineFppfComparison_hasPair :
    DerivedAdjunction.HasPair.{u + 1} (affineFppfComparison X) :=
  sorry

/-- The derived adjunction `ε^* ⊣ Rε_*` of the affine fppf comparison. -/
def affineFppfDerivedAdjunction :
    modulePullbackDerived.{u + 1} (affineFppfComparison X) ⊣
      modulePushforwardDerived.{u + 1} (affineFppfComparison X) :=
  moduleDerivedAdjunction.{u + 1} (affineFppfComparison X)

/-- `affineFppfDerivedAdjunction X` is the canonical derived adjunction of
`affineFppfComparison X`. -/
theorem affineFppfDerivedAdjunction_eq :
    affineFppfDerivedAdjunction X =
      moduleDerivedAdjunction.{u + 1} (affineFppfComparison X) :=
  rfl

/-- Derived pushforward along `ε` is full. -/
instance instAffineFppfComparison_pushforwardDerivedFull :
    (modulePushforwardDerived.{u + 1} (affineFppfComparison X)).Full :=
  sorry

/-- Derived pushforward along `ε` is faithful. -/
instance instAffineFppfComparison_pushforwardDerivedFaithful :
    (modulePushforwardDerived.{u + 1} (affineFppfComparison X)).Faithful :=
  sorry

/-- The object property of derived modules on `𝒳_affine,fppf` whose derived
pushforward along `ε` is quasi-coherent on the chaotic affine site. -/
abbrev affineFppfTargetProperty : ObjectProperty
    (ModuleDerived.{u + 1}
      (ofCommRingSheaf (affineSiteFppfTopology X) (affineFppfStructureSheaf X))) :=
  (qcProperty X).inverseImage
    (modulePushforwardDerived.{u + 1} (affineFppfComparison X))

/-- A derived module satisfies `affineFppfTargetProperty X` if and only if its
derived pushforward along `ε` lies in `qcProperty X`. -/
theorem affineFppfTargetProperty_mem_iff
    (K : ModuleDerived.{u + 1}
      (ofCommRingSheaf (affineSiteFppfTopology X) (affineFppfStructureSheaf X))) :
    affineFppfTargetProperty X K ↔
      qcProperty X
        ((modulePushforwardDerived.{u + 1} (affineFppfComparison X)).obj K) :=
  Iff.rfl

/-- The canonical tensor-sheafification comparison to derived sections on every affine
fppf slice is invertible for every K-flat coefficient complex over the original section ring. -/
theorem affineFppfComparison_kFlatSections_isIso
    (x : affineSite X)
    (M : CochainComplex (_root_.ModuleCat ((affineStructureSheaf X).obj.obj (Opposite.op x))) ℤ)
    (hM : M.IsKFlat) :
    IsIso (TensorSections.comparison (affineStructureSheaf X).obj x
      (affineSiteFppfTopology X) (affineFppfStructureSheaf X)
      (((𝟭 (affineSite X)).sheafAdjunctionContinuous CommRingCat.{u + 1} ⊥
        (affineSiteFppfTopology X)).unit.app (affineStructureSheaf X)).hom M) := sorry

/-- The derived unit of the affine fppf comparison is invertible on quasi-coherent objects. -/
theorem affineFppfComparison_unitCondition :
    qcProperty X ≤ (affineFppfDerivedAdjunction X).unitIsoProperty :=
  sorry

/-- Derived pushforward restricts to an equivalence onto quasi-coherent derived objects. -/
instance affineFppfComparison_pushforwardRestriction_isEquivalence :
    (Adjunction.InverseImageRestriction.right (qcProperty X) :
        (affineFppfTargetProperty X).FullSubcategory ⥤
          (qcProperty X).FullSubcategory).IsEquivalence :=
  Adjunction.InverseImageRestriction.right_isEquivalence
    (affineFppfDerivedAdjunction X) (qcProperty X) (affineFppfComparison_unitCondition X)

/-- Derived pullback restricts to the inverse equivalence on quasi-coherent derived objects. -/
instance affineFppfComparison_pullbackRestriction_isEquivalence :
    (Adjunction.InverseImageRestriction.left (affineFppfDerivedAdjunction X)
      (qcProperty X) (affineFppfComparison_unitCondition X)).IsEquivalence :=
  Adjunction.InverseImageRestriction.left_isEquivalence
    (affineFppfDerivedAdjunction X) (qcProperty X) (affineFppfComparison_unitCondition X)

/-- The affine fppf comparison has the K-flat slice-sections property, its derived unit
is invertible on quasi-coherent objects, and its restricted adjoint functors are equivalences. -/
theorem affineFppfComparison_spec :
    (∀ (x : affineSite X)
      (M : CochainComplex (_root_.ModuleCat ((affineStructureSheaf X).obj.obj (Opposite.op x))) ℤ),
      M.IsKFlat → IsIso (TensorSections.comparison (affineStructureSheaf X).obj x
        (affineSiteFppfTopology X) (affineFppfStructureSheaf X)
        (((𝟭 (affineSite X)).sheafAdjunctionContinuous CommRingCat.{u + 1} ⊥
        (affineSiteFppfTopology X)).unit.app (affineStructureSheaf X)).hom M)) ∧
    (qcProperty X ≤ (affineFppfDerivedAdjunction X).unitIsoProperty) ∧
    (Adjunction.InverseImageRestriction.right (qcProperty X) :
      (affineFppfTargetProperty X).FullSubcategory ⥤
        (qcProperty X).FullSubcategory).IsEquivalence ∧
    (Adjunction.InverseImageRestriction.left (affineFppfDerivedAdjunction X)
      (qcProperty X) (affineFppfComparison_unitCondition X)).IsEquivalence :=
  ⟨affineFppfComparison_kFlatSections_isIso X,
    affineFppfComparison_unitCondition X,
    affineFppfComparison_pushforwardRestriction_isEquivalence X,
    affineFppfComparison_pullbackRestriction_isEquivalence X⟩

end AlgebraicGeometry.GroupoidsOver
