module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.K0
public import ReasLib.AlgebraicGeometry.Scheme.K0
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.AffinePullback.Ambient
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine
public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.Property.Functor
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Nested

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Perfect derived `O_(Spec R)`-modules have quasi-coherent cohomology. -/
theorem K0.perfect_le_derivedQuasiCoherent (R : CommRingCat.{u}) :
    RingedSpace.ModuleDerived.perfect (X := (Spec R).toRingedSpace) ≤
      DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty (Spec R).toRingedSpace) := sorry

/-- The affine derived equivalence identifies perfect objects on both sides. -/
theorem K0.affinePerfect_inverseImage (R : CommRingCat.{u}) :
    ((RingedSpace.ModuleDerived.perfect (X := (Spec R).toRingedSpace)).inverseImage
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty (Spec R).toRingedSpace)).ι).inverseImage
        (DerivedQCoh.affineFunctor R) =
      (DerivedCategory.IsPerfect :
        ObjectProperty (DerivedCategory (ModuleCat R))) := sorry

/-- Perfect objects remain closed under isomorphisms after restriction to derived
quasi-coherent modules on `Spec R`. -/
instance K0.affinePerfect_isClosedUnderIsomorphisms (R : CommRingCat.{u}) :
    ((RingedSpace.ModuleDerived.perfect (X := (Spec R).toRingedSpace)).inverseImage
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty
          (Spec R).toRingedSpace)).ι).IsClosedUnderIsomorphisms := sorry

/-- The affine derived equivalence restricted to perfect objects. -/
noncomputable def K0.affinePerfectEquivalence (R : CommRingCat.{u}) :
    CategoryTheory.PerfectDerived R ≌
      RingedSpace.ModuleDerived.Perfect (X := (Spec R).toRingedSpace) :=
  (((DerivedQCoh.affineModuleEquivalence R).mapDerivedCategory.trans
      (DerivedCategory.CohomologyIn.Comparison.functor
        (RingedSpace.quasiCoherentModuleProperty
          (Spec R).toRingedSpace)).asEquivalence).congrFullSubcategory
      (Q := (RingedSpace.ModuleDerived.perfect
        (X := (Spec R).toRingedSpace)).inverseImage
          (DerivedCategory.cohomologyIn
            (RingedSpace.quasiCoherentModuleProperty (Spec R).toRingedSpace)).ι)
      (K0.affinePerfect_inverseImage R)).trans
    (ObjectProperty.nestedEquivalence
      (RingedSpace.ModuleDerived.perfect (X := (Spec R).toRingedSpace))
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty (Spec R).toRingedSpace))
      (K0.perfect_le_derivedQuasiCoherent R))

/-- The forward affine perfect equivalence is induced by the affine derived functor. -/
theorem K0.affinePerfectEquivalence_functor_obj (R : CommRingCat.{u})
    (K : CategoryTheory.PerfectDerived R) :
    ((K0.affinePerfectEquivalence R).functor.obj K).obj =
      ((DerivedQCoh.affineFunctor R).obj K.obj).obj := sorry

/-- The inverse affine perfect equivalence respects the relations defining triangulated K₀. -/
theorem K0.affineDerivedRelations (R : CommRingCat.{u}) :
    TriangulatedK0.relations
        (RingedSpace.ModuleDerived.Perfect (X := (Spec R).toRingedSpace)) ≤
      (FreeAbelianGroup.lift fun K ↦
        TriangulatedK0.of ((K0.affinePerfectEquivalence R).inverse.obj K)).ker := sorry

/-- The affine perfect equivalence respects the relations defining triangulated K₀. -/
theorem K0.affinePerfectRelations (R : CommRingCat.{u}) :
    TriangulatedK0.relations (CategoryTheory.PerfectDerived R) ≤
      (FreeAbelianGroup.lift fun K ↦
        TriangulatedK0.of ((K0.affinePerfectEquivalence R).functor.obj K)).ker := sorry

/-- The homomorphism from the scheme K₀ of `Spec R` to perfect-derived K₀ induced by
the inverse affine perfect equivalence. -/
noncomputable def K0.affineDerivedToPerfect (R : CommRingCat.{u}) :
    K0 (Spec R) →+ CategoryTheory.PerfectK0 R :=
  TriangulatedK0.lift
    (fun K ↦ TriangulatedK0.of ((K0.affinePerfectEquivalence R).inverse.obj K))
    (K0.affineDerivedRelations R)

/-- The homomorphism from perfect-derived K₀ to the scheme K₀ of `Spec R` induced by
the affine perfect equivalence. -/
noncomputable def K0.perfectToAffineDerived (R : CommRingCat.{u}) :
    CategoryTheory.PerfectK0 R →+ K0 (Spec R) :=
  TriangulatedK0.lift
    (fun K ↦ TriangulatedK0.of ((K0.affinePerfectEquivalence R).functor.obj K))
    (K0.affinePerfectRelations R)

/-- The affine and perfect-derived K₀ homomorphisms are inverse on scheme K₀. -/
theorem K0.affineDerivedLeftInverse (R : CommRingCat.{u}) :
    Function.LeftInverse (K0.perfectToAffineDerived R) (K0.affineDerivedToPerfect R) := sorry

/-- The affine and perfect-derived K₀ homomorphisms are inverse on perfect-derived K₀. -/
theorem K0.affineDerivedRightInverse (R : CommRingCat.{u}) :
    Function.RightInverse (K0.perfectToAffineDerived R) (K0.affineDerivedToPerfect R) := sorry

/-- The additive equivalence from the scheme K₀ of `Spec R` to perfect-derived K₀. -/
noncomputable def K0.affineDerivedEquiv (R : CommRingCat.{u}) :
    K0 (Spec R) ≃+ CategoryTheory.PerfectK0 R where
  toFun := K0.affineDerivedToPerfect R
  invFun := K0.perfectToAffineDerived R
  left_inv := K0.affineDerivedLeftInverse R
  right_inv := K0.affineDerivedRightInverse R
  map_add' := (K0.affineDerivedToPerfect R).map_add

/-- The affine derived K₀ equivalence sends a perfect-sheaf generator to the generator
of its inverse affine image. -/
theorem K0.affineDerivedEquiv_apply_of (R : CommRingCat.{u})
    (K : RingedSpace.ModuleDerived.Perfect (X := (Spec R).toRingedSpace)) :
    K0.affineDerivedEquiv R (TriangulatedK0.of K) =
      TriangulatedK0.of ((K0.affinePerfectEquivalence R).inverse.obj K) := sorry

/-- The affine comparison from scheme K₀ to projective-module K₀ associated to an explicit
perfect-derived comparison. -/
noncomputable def K0.affineEquiv (R : CommRingCat.{u})
    (h : CategoryTheory.K0Comparison R) :
    K0 (Spec R) ≃+ ModuleCat.K0.projective R :=
  (K0.affineDerivedEquiv R).trans h.equiv

/-- The affine projective K₀ comparison sends a perfect-sheaf generator through the supplied
perfect-derived comparison map. -/
theorem K0.affineEquiv_apply_of (R : CommRingCat.{u})
    (h : CategoryTheory.K0Comparison R)
    (K : RingedSpace.ModuleDerived.Perfect (X := (Spec R).toRingedSpace)) :
    K0.affineEquiv R h (TriangulatedK0.of K) =
      h.map (TriangulatedK0.of ((K0.affinePerfectEquivalence R).inverse.obj K)) := sorry

namespace K0

/-- For an affine scheme `Spec R`, scheme K₀ and projective-module K₀ are additively
equivalent. -/
theorem exists_affineEquiv (R : CommRingCat.{u}) :
    Nonempty (K0 (Spec R) ≃+ ModuleCat.K0.projective R) := sorry

end K0

/-- Coherent modules on `Spec R` are quasi-coherent. -/
theorem K0'.coherent_le_quasicoherent (R : CommRingCat.{u}) [IsNoetherianRing R] :
    SheafOfModules.isCoherent (Spec R).toRingedSpace.ringCatSheaf ≤
      SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf := sorry

/-- Under the affine module equivalence, coherence is exactly finite generation. -/
theorem K0'.affineCoherent_inverseImage (R : CommRingCat.{u}) [IsNoetherianRing R] :
    ((SheafOfModules.isCoherent (Spec R).toRingedSpace.ringCatSheaf).inverseImage
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι).inverseImage
          (AlgebraicGeometry.tildeEquiv : ModuleCat R ≌
            (SheafOfModules.isQuasicoherent
              (Spec R).ringCatSheaf).FullSubcategory).functor =
      ModuleCat.isFG R := sorry

/-- The affine equivalence between finite modules and coherent module sheaves. -/
noncomputable def K0'.affineCoherentEquivalence (R : CommRingCat.{u})
    [IsNoetherianRing R] :
    FGModuleCat R ≌
      (SheafOfModules.isCoherent
        (Spec R).toRingedSpace.ringCatSheaf).FullSubcategory :=
  ((AlgebraicGeometry.tildeEquiv : ModuleCat R ≌
      (SheafOfModules.isQuasicoherent
        (Spec R).ringCatSheaf).FullSubcategory).congrFullSubcategory
      (Q := (SheafOfModules.isCoherent
        (Spec R).toRingedSpace.ringCatSheaf).inverseImage
          (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι)
      (K0'.affineCoherent_inverseImage R)).trans
    (ObjectProperty.nestedEquivalence
      (SheafOfModules.isCoherent (Spec R).toRingedSpace.ringCatSheaf)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
      (K0'.coherent_le_quasicoherent R))

/-- The inverse affine coherent equivalence respects the relations defining coherent-sheaf
K₀. -/
theorem K0'.affineCoherentRelations (R : CommRingCat.{u}) [IsNoetherianRing R] :
    ObjectProperty.GrothendieckGroup.relations
        (SheafOfModules.isCoherent (Spec R).toRingedSpace.ringCatSheaf) ≤
      (FreeAbelianGroup.lift fun F ↦
        ModuleCat.K0.finiteOf R ((K0'.affineCoherentEquivalence R).inverse.obj F)).ker := sorry

/-- The affine coherent equivalence respects the relations defining finite-module K₀. -/
theorem K0'.affineFiniteRelations (R : CommRingCat.{u}) [IsNoetherianRing R] :
    ObjectProperty.GrothendieckGroup.relations (ModuleCat.isFG R) ≤
      (FreeAbelianGroup.lift fun M ↦
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent (Spec R).toRingedSpace.ringCatSheaf)
          ((K0'.affineCoherentEquivalence R).functor.obj M)).ker := sorry

/-- The homomorphism from coherent-sheaf K₀ on `Spec R` to finite-module K₀. -/
noncomputable def K0'.affineCoherentToFinite (R : CommRingCat.{u})
    [IsNoetherianRing R] : K0' (Spec R) →+ ModuleCat.K0.finite R :=
  ObjectProperty.GrothendieckGroup.lift
    (fun F ↦ ModuleCat.K0.finiteOf R ((K0'.affineCoherentEquivalence R).inverse.obj F))
    (K0'.affineCoherentRelations R)

/-- The homomorphism from finite-module K₀ to coherent-sheaf K₀ on `Spec R`. -/
noncomputable def K0'.affineFiniteToCoherent (R : CommRingCat.{u})
    [IsNoetherianRing R] : ModuleCat.K0.finite R →+ K0' (Spec R) :=
  ObjectProperty.GrothendieckGroup.lift
    (fun M ↦ ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.isCoherent (Spec R).toRingedSpace.ringCatSheaf)
      ((K0'.affineCoherentEquivalence R).functor.obj M))
    (K0'.affineFiniteRelations R)

/-- The affine coherent and finite-module K₀ homomorphisms are inverse on coherent-sheaf K₀. -/
theorem K0'.affineCoherentLeftInverse (R : CommRingCat.{u}) [IsNoetherianRing R] :
    Function.LeftInverse (K0'.affineFiniteToCoherent R)
      (K0'.affineCoherentToFinite R) := sorry

/-- The affine coherent and finite-module K₀ homomorphisms are inverse on finite-module K₀. -/
theorem K0'.affineCoherentRightInverse (R : CommRingCat.{u}) [IsNoetherianRing R] :
    Function.RightInverse (K0'.affineFiniteToCoherent R)
      (K0'.affineCoherentToFinite R) := sorry

namespace K0'

/-- The additive equivalence between coherent-sheaf K₀ on `Spec R` and finite-module K₀. -/
noncomputable def affineEquiv (R : CommRingCat.{u}) [IsNoetherianRing R] :
    K0' (Spec R) ≃+ ModuleCat.K0.finite R where
  toFun := K0'.affineCoherentToFinite R
  invFun := K0'.affineFiniteToCoherent R
  left_inv := K0'.affineCoherentLeftInverse R
  right_inv := K0'.affineCoherentRightInverse R
  map_add' := (K0'.affineCoherentToFinite R).map_add

end K0'

/-- The affine coherent K₀ equivalence sends a coherent-sheaf generator to the finite class
of its affine global-sections module. -/
theorem K0'.affineEquiv_apply_of (R : CommRingCat.{u}) [IsNoetherianRing R]
    (F : (SheafOfModules.isCoherent
      (Spec R).toRingedSpace.ringCatSheaf).FullSubcategory) :
    K0'.affineEquiv R
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.isCoherent (Spec R).toRingedSpace.ringCatSheaf) F) =
      ModuleCat.K0.finiteOf R ((K0'.affineCoherentEquivalence R).inverse.obj F) := sorry

/-- The inverse affine coherent K₀ equivalence sends a finite-module generator to the class
of its associated coherent module sheaf. -/
theorem K0'.affineEquiv_symm_apply_of (R : CommRingCat.{u}) [IsNoetherianRing R]
    (M : FGModuleCat R) :
    (K0'.affineEquiv R).symm (ModuleCat.K0.finiteOf R M) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.isCoherent (Spec R).toRingedSpace.ringCatSheaf)
        ((K0'.affineCoherentEquivalence R).functor.obj M) := sorry

end AlgebraicGeometry.Scheme
