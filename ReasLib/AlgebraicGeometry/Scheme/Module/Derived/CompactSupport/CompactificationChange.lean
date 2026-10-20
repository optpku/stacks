/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.SourceRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Compactification
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.Composition

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
open Cohomology DeligneSystem
variable {k : Type u} [Field k] {X Y U : Scheme.{u}}
variable [IsNoetherian X] [IsNoetherian Y] [IsNoetherian U]
variable (f : X ⟶ Y) [IsProper f]
variable (q : Y ⟶ Spec (CommRingCat.of k)) [IsProper q]

/-- Derived sections of proper pushforward are compared by the actual
sections-pushforward and ground-field scalar-composition isomorphisms. -/
def refinementGlobalSectionsIso (E : RingedSpace.ModuleDerived X.toRingedSpace) (d : ℤ) :
    (globalCohomologyOverField (f ≫ q) d).obj E ≅
      (globalCohomologyOverField q d).obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} k) d).mapIso
    (ModuleCat.DerivedRestriction.compObjIsoOfEq q.globalSectionsMap f.appTop.hom
        (f ≫ q).globalSectionsMap (IdealDuality.sectionScalars_comp q f)
        ((RingedSpace.moduleDerivedGlobalSections X.toRingedSpace).obj E) ≪≫
      (ModuleCat.derivedRestrictionOfScalars q.globalSectionsMap).mapIso
        ((RingedSpace.Module.Derived.GlobalSections.pushforwardIso f.toShHom).app E))

/-- Bounded proper pushforward commutes with ordinary cohomology over the
field through the specified ambient and sections comparisons. -/
def refinementCohomologyIso (d : ℤ) :
    properPushforward f ⋙ overFieldFunctor q d ≅ overFieldFunctor (f ≫ q) d :=
  NatIso.ofComponents (fun L ↦
    ((boundedSectionsIso q d).app ((properPushforward f).obj L)).symm ≪≫
      (globalCohomologyOverField q d).mapIso ((properPushforward.ambientIso f).app L) ≪≫
      (refinementGlobalSectionsIso f q L.obj.obj d).symm ≪≫
      (boundedSectionsIso (f ≫ q) d).app L)
    (fun _ ↦ sorry)

/-- Compact cohomology changes along a proper refinement by realizing the
unique interior-counit-normalized Deligne comparison and then proper pushforward.
The construction is independent of horizontal duality. -/
def compactRefinementIso (j' : U ⟶ X) (j : U ⟶ Y)
    [IsOpenImmersion j'] [IsOpenImmersion j] (h : j' ≫ f = j)
    (L : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) (d : ℤ) :
    cohomology q (boundedTower j (extension j L)) d ≅
      cohomology (f ≫ q) (boundedTower j' (extension j' L)) d :=
  Pro.ModuleLimit.mapIso (overFieldFunctor q d)
      (iso_extensionByZero_properPushforwardLimAlong f j' j h L) ≪≫
    HasLimit.isoOfNatIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (boundedTower j' (extension j' L)) (refinementCohomologyIso f q d))

/-- The proper trace between normalized q!O objects is the adjunct of the
composite structural counit, with the actual pushforward composition map. -/
def refinementTrace :
    (Scheme.DerivedQCoh.pushforwardCohomologyIn f).obj
        (Scheme.DerivedQCoh.properDualizingComplex (f ≫ q)) ⟶
      Scheme.DerivedQCoh.properDualizingComplex q :=
  ((Adjunction.ofIsLeftAdjoint (Scheme.DerivedQCoh.pushforwardCohomologyIn q)).homEquiv _ _)
    ((Scheme.DerivedQCoh.pushforwardCompIso f q
        (RingedSpace.modulePullbackDerived.compComparison_isIso f.toShHom q.toShHom)).hom.app
          (Scheme.DerivedQCoh.properDualizingComplex (f ≫ q)) ≫
      (Adjunction.ofIsLeftAdjoint (Scheme.DerivedQCoh.pushforwardCohomologyIn (f ≫ q))).counit.app
        (Scheme.DerivedQCoh.structureSheaf (Spec (CommRingCat.of k))))

/-- The actual restriction of proper pushforward to the fixed interior is
mapped to the original complex by the pullback-pushforward counit. -/
def refinementInteriorCounit (j' : U ⟶ X) (j : U ⟶ Y)
    [IsOpenImmersion j'] [IsOpenImmersion j] (h : j' ≫ f = j)
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    (RingedSpace.modulePullbackDerived j.toShHom).obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E) ⟶
      (RingedSpace.modulePullbackDerived j'.toShHom).obj E :=
  -- Local instance justification (proof-local temporary data): use the existing geometric adjunction certificate for this fixed proper morphism.
  letI := properPushforwardAlong_derivedPair f
  (eqToIso (congrArg (fun a : U ⟶ Y ↦ RingedSpace.modulePullbackDerived a.toShHom) h)).inv.app
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E) ≫
    (RingedSpace.modulePullbackDerived.compIso j'.toShHom f.toShHom
      (RingedSpace.modulePullbackDerived.compComparison_isIso j'.toShHom f.toShHom)).inv.app
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E) ≫
    (RingedSpace.modulePullbackDerived j'.toShHom).map
      ((RingedSpace.modulePullbackDerivedPushforwardAdjunction f.toShHom).counit.app E)

/-- A proper refinement with dense interior is an isomorphism over the
target interior, hence its specified interior counit is invertible. -/
theorem refinementInteriorCounit_isIso (j' : U ⟶ X) (j : U ⟶ Y)
    [IsOpenImmersion j'] [IsOpenImmersion j] [IsDominant j'] (h : j' ≫ f = j)
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    IsIso (refinementInteriorCounit f j' j h E) := sorry

/-- On the dense fixed interior, normalized dualizing objects change by the
inverse interior counit followed by restriction of the actual proper trace. -/
def refinementDualizingMap (j' : U ⟶ X) (j : U ⟶ Y)
    [IsOpenImmersion j'] [IsOpenImmersion j] [IsDominant j'] (h : j' ≫ f = j) :
    openDualizing (f ≫ q) j' ⟶ openDualizing q j :=
  (@asIso _ _ _ _
    (refinementInteriorCounit f j' j h (Scheme.DerivedQCoh.properDualizingComplex (f ≫ q)).obj)
    (refinementInteriorCounit_isIso f j' j h
      (Scheme.DerivedQCoh.properDualizingComplex (f ≫ q)).obj)).inv ≫
    (RingedSpace.modulePullbackDerived j.toShHom).map
      ((refinementTrace f q).hom)

/-- The proper trace is an isomorphism on the common dense interior, where
the proper refinement is an isomorphism of schemes. -/
theorem refinementDualizingMap_isIso (j' : U ⟶ X) (j : U ⟶ Y)
    [IsOpenImmersion j'] [IsOpenImmersion j] [IsDominant j'] (h : j' ≫ f = j) :
    IsIso (refinementDualizingMap f q j' j h) := sorry

/-- The dualizing comparison inverts only the specified interior trace map. -/
def refinementDualizingIso (j' : U ⟶ X) (j : U ⟶ Y)
    [IsOpenImmersion j'] [IsOpenImmersion j] [IsDominant j'] (h : j' ≫ f = j) :
    openDualizing (f ≫ q) j' ≅ openDualizing q j :=
  @asIso _ _ _ _ (refinementDualizingMap f q j' j h)
    (refinementDualizingMap_isIso f q j' j h)

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
open Scheme.Compactification Cohomology DeligneSystem
variable {k : Type u} [Field k]
variable (U : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))

/-- Compact cohomology of a fixed bounded coherent coefficient in a specified
proper compactification, with its actual Deligne tower. -/
abbrev compactificationCohomology (P : Of (Spec (CommRingCat.of k)) U.obj)
    (L : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) : ModuleCat.{u} k :=
  cohomology P.obj.right.hom (boundedTower (Of.ι P) (extension (Of.ι P) L)) d

/-- Every map of compactifications over the field is proper. -/
theorem compactificationMap_isProper {P Q : Of (Spec (CommRingCat.of k)) U.obj} (g : P ⟶ Q) :
    IsProper (Of.ambientMap g) := sorry

/-- The ambient map of a refinement preserves the structure morphism. -/
theorem compactificationMap_base {P Q : Of (Spec (CommRingCat.of k)) U.obj} (g : P ⟶ Q) :
    Of.ambientMap g ≫ Q.obj.right.hom = P.obj.right.hom := g.hom.right.w

/-- A compactification arrow changes compact cohomology by the actual
proper-pushforward realization, with only its structural equality transported. -/
def compactificationArrowIso {P Q : Of (Spec (CommRingCat.of k)) U.obj} (g : P ⟶ Q)
    (L : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :
    compactificationCohomology U Q L d ≅ compactificationCohomology U P L d :=
  -- Local instance justification (proof-local temporary data): properness follows from this map of proper compactifications over the field.
  letI := compactificationMap_isProper U g
  compactRefinementIso (Of.ambientMap g) Q.obj.right.hom (Of.ι P) (Of.ι Q)
      (Of.ι_comp_ambientMap g) L d ≪≫
    eqToIso (congrArg
      (fun q ↦ cohomology q (boundedTower (Of.ι P) (extension (Of.ι P) L)) d)
      (compactificationMap_base U g))

/-- A dense refinement changes q!O on the fixed interior by the specified trace. -/
def openDualizingIsoOfEq {Z V : Scheme.{u}} (a b : Z ⟶ Spec (CommRingCat.of k))
    [IsProper a] [IsProper b] (j : V ⟶ Z) [IsOpenImmersion j] (h : a = b) :
    openDualizing a j ≅ openDualizing b j :=
  h ▸ Iso.refl _

/-- A dense refinement changes q!O on the fixed interior by the specified trace. -/
def compactificationDualizingArrowIso {P Q : Of (Spec (CommRingCat.of k)) U.obj}
    (g : P ⟶ Q) [IsDominant (Of.ι P)] :
    openDualizing P.obj.right.hom (Of.ι P) ≅ openDualizing Q.obj.right.hom (Of.ι Q) :=
  -- Local instance justification (proof-local temporary data): properness follows from this map of proper compactifications over the field.
  letI := compactificationMap_isProper U g
  openDualizingIsoOfEq P.obj.right.hom (Of.ambientMap g ≫ Q.obj.right.hom) (Of.ι P)
      (compactificationMap_base U g).symm ≪≫
    refinementDualizingIso (Of.ambientMap g) Q.obj.right.hom (Of.ι P) (Of.ι Q)
      (Of.ι_comp_ambientMap g)

/-- The existing cofiltered compactification and initial dense-interior owners
choose a common dense refinement; no comparison isomorphism is chosen. -/
def denseCommonCompactification (P Q : Of (Spec (CommRingCat.of k)) U.obj) :
    DenseOf (Spec (CommRingCat.of k)) U.obj :=
  -- Local instance justification (proof-local temporary data): P itself witnesses that the fixed-interior compactification category is nonempty.
  letI : Nonempty (Of (Spec (CommRingCat.of k)) U.obj) := ⟨P⟩
  Functor.Initial.lift (DenseOf.inclusion (Spec (CommRingCat.of k)) U.obj)
    (IsCofiltered.min P Q)

/-- The specified common-refinement arrow to the first compactification. -/
def denseCommonToLeft (P Q : Of (Spec (CommRingCat.of k)) U.obj) :
    (denseCommonCompactification U P Q).obj ⟶ P :=
  -- Local instance justification (proof-local temporary data): use the existing object P for the cofiltered-category nonemptiness boundary.
  letI : Nonempty (Of (Spec (CommRingCat.of k)) U.obj) := ⟨P⟩
  Functor.Initial.homToLift (DenseOf.inclusion (Spec (CommRingCat.of k)) U.obj)
      (IsCofiltered.min P Q) ≫ IsCofiltered.minToLeft P Q

/-- The specified common-refinement arrow to the second compactification. -/
def denseCommonToRight (P Q : Of (Spec (CommRingCat.of k)) U.obj) :
    (denseCommonCompactification U P Q).obj ⟶ Q :=
  -- Local instance justification (proof-local temporary data): use the existing object P for the cofiltered-category nonemptiness boundary.
  letI : Nonempty (Of (Spec (CommRingCat.of k)) U.obj) := ⟨P⟩
  Functor.Initial.homToLift (DenseOf.inclusion (Spec (CommRingCat.of k)) U.obj)
      (IsCofiltered.min P Q) ≫ IsCofiltered.minToRight P Q

/-- Actual compactification-change transport on compact cohomology, formed
from proper pushforward along the two specified common-refinement arrows. -/
def compactificationCohomologyIso (P Q : Of (Spec (CommRingCat.of k)) U.obj)
    (L : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :
    compactificationCohomology U P L d ≅ compactificationCohomology U Q L d :=
  compactificationArrowIso U (denseCommonToLeft U P Q) L d ≪≫
    (compactificationArrowIso U (denseCommonToRight U P Q) L d).symm

/-- The geometric compactification-change isomorphism preserves the inverse-
limit topology on compact cohomology. -/
theorem compactificationCohomologyIso_topology (P Q : Of (Spec (CommRingCat.of k)) U.obj)
    (L : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :
    cohomologyTopology P.obj.right.hom (boundedTower (Of.ι P) (extension (Of.ι P) L)) d =
      TopologicalSpace.induced (compactificationCohomologyIso U P Q L d).hom
        (cohomologyTopology Q.obj.right.hom (boundedTower (Of.ι Q) (extension (Of.ι Q) L)) d) := sorry

/-- The normalized dualizing-object change uses proper traces on the common
dense refinement, with no bare IsIsomorphic extraction. -/
def compactificationDualizingIso (P Q : Of (Spec (CommRingCat.of k)) U.obj) :
    openDualizing P.obj.right.hom (Of.ι P) ≅ openDualizing Q.obj.right.hom (Of.ι Q) :=
  -- Local instance justification (proof-local temporary data): density is a field of the selected dense common compactification.
  letI := (denseCommonCompactification U P Q).property.isDominant
  (compactificationDualizingArrowIso U (denseCommonToLeft U P Q)).symm ≪≫
    compactificationDualizingArrowIso U (denseCommonToRight U P Q)

/-- The compact-cohomology change agrees with the construction from every
common refinement, so the auxiliary cofiltered choice does not affect it. -/
theorem compactificationCohomologyIso_eq_refinement
    (P Q R : Of (Spec (CommRingCat.of k)) U.obj) (a : R ⟶ P) (b : R ⟶ Q)
    (L : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :
    compactificationCohomologyIso U P Q L d =
      compactificationArrowIso U a L d ≪≫ (compactificationArrowIso U b L d).symm := sorry

/-- The normalized dualizing comparison agrees with the proper-trace
construction from every dense common refinement. -/
theorem compactificationDualizingIso_eq_refinement
    (P Q R : Of (Spec (CommRingCat.of k)) U.obj) [IsDominant (Of.ι R)]
    (a : R ⟶ P) (b : R ⟶ Q) :
    compactificationDualizingIso U P Q =
      (compactificationDualizingArrowIso U a).symm ≪≫ compactificationDualizingArrowIso U b := sorry

open RingedSpace.ModuleDerived.KFlat CategoryTheory.MonoidalClosed
variable [HomotopyTensorDescends U.obj.left.toRingedSpace]
variable [TensorDescends U.obj.left.toRingedSpace] [IsLocalization U.obj.left.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived U.obj.left.toRingedSpace)]

/-- The actual change of normalized dual coefficients applies RHom(K,-)
to the trace-normalized dualizing comparison and lifts it fully faithfully. -/
def normalizedDualChange (P Q : Of (Spec (CommRingCat.of k)) U.obj)
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) :
    normalizedSourceDual P.obj.right.hom (Of.ι P) K ≅
      normalizedSourceDual Q.obj.right.hom (Of.ι Q) K :=
  (ambient (SheafOfModules.isCoherent U.obj.left.ringCatSheaf)).preimageIso
    ((ihom K.obj.obj).mapIso (compactificationDualizingIso U P Q))

/-- Change both the normalized dual coefficient and the compact-support
presentation by actual geometric maps, independently of horizontal duality. -/
def normalizedCompactificationIso (P Q : Of (Spec (CommRingCat.of k)) U.obj)
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :
    compactificationCohomology U P (normalizedSourceDual P.obj.right.hom (Of.ι P) K) d ≅
      compactificationCohomology U Q (normalizedSourceDual Q.obj.right.hom (Of.ι Q) K) d :=
  Pro.ModuleLimit.mapIso (overFieldFunctor P.obj.right.hom d)
      ((extensionByZero (Of.ι P)).mapIso (normalizedDualChange U P Q K)) ≪≫
    compactificationCohomologyIso U P Q (normalizedSourceDual Q.obj.right.hom (Of.ι Q) K) d

/-- Normalized compactification change is the identity for an unchanged model. -/
theorem normalizedCompactificationIso_refl (P : Of (Spec (CommRingCat.of k)) U.obj)
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :
    normalizedCompactificationIso U P P K d = Iso.refl _ := sorry

/-- Actual normalized compactification changes satisfy the cocycle law. -/
theorem normalizedCompactificationIso_trans (P Q R : Of (Spec (CommRingCat.of k)) U.obj)
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :
    normalizedCompactificationIso U P Q K d ≪≫ normalizedCompactificationIso U Q R K d =
      normalizedCompactificationIso U P R K d := sorry

/-- Changing normalized dual coefficients and compactification preserves
the actual compact-support inverse-limit topology. -/
theorem normalizedCompactificationIso_topology (P Q : Of (Spec (CommRingCat.of k)) U.obj)
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :
    cohomologyTopology P.obj.right.hom (boundedTower (Of.ι P) (extension (Of.ι P)
        (normalizedSourceDual P.obj.right.hom (Of.ι P) K))) d =
      TopologicalSpace.induced (normalizedCompactificationIso U P Q K d).hom
        (cohomologyTopology Q.obj.right.hom (boundedTower (Of.ι Q) (extension (Of.ι Q)
          (normalizedSourceDual Q.obj.right.hom (Of.ι Q) K))) d) := sorry

variable (U' : Scheme.FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))

/-- The smaller open inherits a genuine compactification from any
compactification of the larger open, with the original structure morphism. -/
def restrictedCompactification (i : U' ⟶ U) [IsOpenImmersion i.hom.left]
    (P : Of (Spec (CommRingCat.of k)) U.obj) : Of (Spec (CommRingCat.of k)) U'.obj :=
  -- Local instance justification (defeq pin): expose the interior of P before composing the two open immersions in the Over category.
  letI : IsOpenImmersion (i.hom ≫ P.obj.hom).left :=
    inferInstanceAs (IsOpenImmersion (i.hom.left ≫ Of.ι P))
  Of.mk (Spec (CommRingCat.of k)) P.obj.right (i.hom ≫ P.obj.hom)

variable [HomotopyTensorDescends U'.obj.left.toRingedSpace]
variable [TensorDescends U'.obj.left.toRingedSpace] [IsLocalization U'.obj.left.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived U'.obj.left.toRingedSpace)]

/-- Actual compactification-change transport commutes with the geometric
compact restriction, including its normalized dual coefficient comparison.
This is a law of the constructed maps, never a compatibility input. -/
theorem normalizedCompactificationIso_openRestriction
    (i : U' ⟶ U) [IsOpenImmersion i.hom.left]
    (P Q : Of (Spec (CommRingCat.of k)) U.obj)
    [HomotopyTensorDescends P.obj.right.left.toRingedSpace]
    [TensorDescends P.obj.right.left.toRingedSpace] [IsLocalization P.obj.right.left.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived P.obj.right.left.toRingedSpace)]
    [HomotopyTensorDescends Q.obj.right.left.toRingedSpace]
    [TensorDescends Q.obj.right.left.toRingedSpace] [IsLocalization Q.obj.right.left.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived Q.obj.right.left.toRingedSpace)]
    (K : Dᵇ[SheafOfModules.isCoherent U.obj.left.ringCatSheaf]) (d : ℤ) :
    (normalizedCompactificationIso U'
        (restrictedCompactification U U' i P) (restrictedCompactification U U' i Q)
        ((restriction i.hom.left).obj K) d).hom ≫
      normalizedCompactRestriction Q.obj.right.hom (Of.ι Q) i.hom.left K d =
    normalizedCompactRestriction P.obj.right.hom (Of.ι P) i.hom.left K d ≫
      (normalizedCompactificationIso U P Q K d).hom := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
