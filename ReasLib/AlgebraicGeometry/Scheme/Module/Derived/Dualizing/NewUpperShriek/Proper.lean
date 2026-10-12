/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.Assignment
public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.Base
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Pseudofunctor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coherent.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.PlusModel
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.SheafyTrace.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Coherent cohomology on a locally Noetherian scheme is quasicoherent cohomology in the
unbounded derived category. -/
theorem coherentCohomology_le_quasicoherentCohomologyUnbounded (X : Scheme.{u})
    [IsLocallyNoetherian X] :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ≤
      DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) := sorry

/-- The canonical inclusion from complexes with coherent cohomology to derived
quasicoherent complexes. -/
noncomputable def coherentInclusion (X : Scheme.{u}) [IsLocallyNoetherian X] :
    D[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf] ⥤ DerivedQCoh X :=
  ObjectProperty.ιOfLE (coherentCohomology_le_quasicoherentCohomologyUnbounded X)

/-- The underlying unbounded derived object of `coherentInclusion X` is unchanged. -/
theorem coherentInclusion_obj_obj (X : Scheme.{u}) [IsLocallyNoetherian X]
    (K : D[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]) :
    ((coherentInclusion X).obj K).obj = K.obj := sorry

/-- The canonical passage from bounded-above coherent complexes to derived
quasicoherent complexes. -/
noncomputable def coherentMinusToDerivedQCoh (X : Scheme.{u}) [IsLocallyNoetherian X] :
    D⁻[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf] ⥤ DerivedQCoh X :=
  DerivedCategory.Minus.CohomologyIn.toUnbounded
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) ⋙ coherentInclusion X

/-- Forgetting boundedness and coherence through `coherentMinusToDerivedQCoh` leaves the
underlying derived object unchanged. -/
theorem coherentMinusToDerivedQCoh_obj_obj (X : Scheme.{u}) [IsLocallyNoetherian X]
    (K : D⁻[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]) :
    ((coherentMinusToDerivedQCoh X).obj K).obj = K.obj.obj := sorry

/-- The canonical passage from bounded-below coherent complexes to derived
quasicoherent complexes. -/
noncomputable def coherentPlusToDerivedQCoh (X : Scheme.{u}) [IsLocallyNoetherian X] :
    D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf] ⥤ DerivedQCoh X :=
  coherentPlusInclusion X ⋙ DerivedCategory.Plus.CohomologyIn.toUnbounded
    (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)

/-- Forgetting boundedness and coherence through `coherentPlusToDerivedQCoh` leaves the
underlying derived object unchanged. -/
theorem coherentPlusToDerivedQCoh_obj_obj (X : Scheme.{u}) [IsLocallyNoetherian X]
    (K : D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]) :
    ((coherentPlusToDerivedQCoh X).obj K).obj = K.obj.obj := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh

namespace AlgebraicGeometry.Scheme.NewUpperShriekAssignment

variable {S : Scheme.{u}} [IsNoetherian S]
variable [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
variable {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
variable {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}

/-- A proper right-adjoint model takes bounded-below coherent inputs to objects with
bounded-below coherent cohomology. -/
theorem properRestriction_coherent {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeOver S} (f : X ⟶ Y)
    [IsProper f.hom.left] (A : DerivedQCoh.PlusRightAdjoint f.hom.left)
    (K : D⁺[SheafOfModules.isCoherent Y.obj.left.toRingedSpace.ringCatSheaf]) :
    DerivedCategory.Plus.cohomologyIn
      (SheafOfModules.isCoherent X.obj.left.toRingedSpace.ringCatSheaf)
      (((DerivedQCoh.coherentPlusInclusion Y.obj.left ⋙ A.plus) ⋙
        (DerivedCategory.Plus.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.obj.left.toRingedSpace)).ι).obj K) := sorry

/-- The restriction of a chosen proper right adjoint to bounded-below coherent objects. -/
noncomputable def properRestriction {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeOver S} (f : X ⟶ Y)
    [IsProper f.hom.left] (A : DerivedQCoh.PlusRightAdjoint f.hom.left) :
    D⁺[SheafOfModules.isCoherent Y.obj.left.toRingedSpace.ringCatSheaf] ⥤
      D⁺[SheafOfModules.isCoherent X.obj.left.toRingedSpace.ringCatSheaf] :=
  (DerivedCategory.Plus.cohomologyIn
    (SheafOfModules.isCoherent X.obj.left.toRingedSpace.ringCatSheaf)).lift
      ((DerivedQCoh.coherentPlusInclusion Y.obj.left ⋙ A.plus) ⋙
        (DerivedCategory.Plus.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.obj.left.toRingedSpace)).ι)
      (properRestriction_coherent f A)

/-- The underlying bounded-below derived object of the proper restriction is the value of
the chosen bounded-below right-adjoint model. -/
theorem properRestriction_obj_obj {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeOver S} (f : X ⟶ Y)
    [IsProper f.hom.left] (A : DerivedQCoh.PlusRightAdjoint f.hom.left)
    (K : D⁺[SheafOfModules.isCoherent Y.obj.left.toRingedSpace.ringCatSheaf]) :
    ((properRestriction f A).obj K).obj =
      (A.plus.obj ((DerivedQCoh.coherentPlusInclusion Y.obj.left).obj K)).obj := sorry

/-- Forgetting all boundedness and cohomology conditions identifies the proper restriction
with the bounded-below right-adjoint model. -/
theorem properRestriction_obj_obj_obj
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) [IsProper f.hom.left]
    (A : DerivedQCoh.PlusRightAdjoint f.hom.left) (M : DerivedCoh.Plus Y.obj.left) :
    ((properRestriction f A).obj M).obj.obj =
      (A.plus.obj ((DerivedQCoh.coherentPlusInclusion Y.obj.left).obj M)).obj.obj := sorry

/-- Forgetting all boundedness and cohomology conditions identifies the proper restriction
with the bounded-below right-adjoint model. -/
noncomputable def properRestrictionToPlusAmbientIso
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) [IsProper f.hom.left]
    (A : DerivedQCoh.PlusRightAdjoint f.hom.left) (M : DerivedCoh.Plus Y.obj.left) :
    ((properRestriction f A).obj M).obj.obj ≅
      (A.plus.obj ((DerivedQCoh.coherentPlusInclusion Y.obj.left).obj M)).obj.obj :=
  eqToIso (properRestriction_obj_obj_obj f A M)

/-- For a proper morphism, new upper shriek is the coherent bounded-below restriction of
any chosen right adjoint to derived quasicoherent pushforward. -/
theorem properRestriction_isIsomorphic
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y)
    [IsProper f.hom.left] (A : DerivedQCoh.PlusRightAdjoint f.hom.left) :
    IsIsomorphic (D.map f) (properRestriction f A) := sorry

/-- The comparison with a chosen proper right adjoint, after forgetting the bounded and
coherent subcategories. -/
noncomputable def properRestrictionAmbientIso
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) [IsProper f.hom.left]
    (A : DerivedQCoh.PlusRightAdjoint f.hom.left)
    (comparison : D.map f ≅ properRestriction f A)
    (M : DerivedCoh.Plus Y.obj.left) :
    ((D.map f).obj M).obj.obj ≅
      (A.right.obj ((DerivedQCoh.coherentPlusToDerivedQCoh Y.obj.left).obj M)).obj :=
    (DerivedCategory.Plus.CohomologyIn.ambient
      (SheafOfModules.isCoherent X.obj.left.toRingedSpace.ringCatSheaf)).mapIso
      (comparison.app M) ≪≫
    properRestrictionToPlusAmbientIso f A M ≪≫
    (DerivedQCoh.inclusion X.obj.left).mapIso
      (A.restrictionIso.app ((DerivedQCoh.coherentPlusInclusion Y.obj.left).obj M))

/-- The proper trace morphism for new upper shriek, obtained by transporting the named
right-adjoint trace morphism through an explicit comparison with `D.map f`. -/
noncomputable def properTraceMap
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) [IsProper f.hom.left]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.hom.left.toShHom)]
    [pullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _ (D.monoidal Y)
      (RingedSpace.ModuleDerived X.obj.left.toRingedSpace) _ (D.monoidal X)
      (RingedSpace.modulePullbackDerived f.hom.left.toShHom)]
    (A : DerivedQCoh.PlusRightAdjoint f.hom.left)
    (comparison : D.map f ≅ properRestriction f A)
    (K : D⁻[SheafOfModules.isCoherent X.obj.left.toRingedSpace.ringCatSheaf])
    (M : DerivedCoh.Plus Y.obj.left) :
    (RingedSpace.moduleDerivedPushforward f.hom.left.toShHom).obj
        ((@MonoidalClosed.ihomOf _ _ (D.monoidal X) (D.closed X) K.obj.obj).obj
          ((D.map f).obj M).obj.obj) ⟶
      (@MonoidalClosed.ihomOf _ _ (D.monoidal Y) (D.closed Y)
        ((RingedSpace.moduleDerivedPushforward f.hom.left.toShHom).obj K.obj.obj)).obj
          M.obj.obj :=
  (RingedSpace.moduleDerivedPushforward f.hom.left.toShHom).map
      ((@MonoidalClosed.ihomOf _ _ (D.monoidal X) (D.closed X) K.obj.obj).map
        (D.properRestrictionAmbientIso f A comparison M).hom) ≫
    @DerivedQCoh.uncoheratedSheafyTraceMap X.obj.left Y.obj.left f.hom.left
      inferInstance inferInstance inferInstance
      (D.homotopyTensorDescends X) (D.tensorDescends X) (D.isLocalization X)
      (D.homotopyTensorDescends Y) (D.tensorDescends Y) (D.isLocalization Y)
      (D.closed X) (D.closed Y) inferInstance pullbackMonoidal A.right A.adjunction
      ((DerivedQCoh.coherentMinusToDerivedQCoh X.obj.left).obj K)
      ((DerivedQCoh.coherentPlusToDerivedQCoh Y.obj.left).obj M)

/-- For a proper morphism, the transported named trace morphism for new upper shriek is
invertible on bounded coherent inputs. -/
theorem properTraceMap_isIso
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y) [IsProper f.hom.left]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.hom.left.toShHom)]
    [pullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _ (D.monoidal Y)
      (RingedSpace.ModuleDerived X.obj.left.toRingedSpace) _ (D.monoidal X)
      (RingedSpace.modulePullbackDerived f.hom.left.toShHom)]
    (A : DerivedQCoh.PlusRightAdjoint f.hom.left)
    (comparison : D.map f ≅ properRestriction f A)
    (K : D⁻[SheafOfModules.isCoherent X.obj.left.toRingedSpace.ringCatSheaf])
    (M : DerivedCoh.Plus Y.obj.left) :
    IsIso (D.properTraceMap f A comparison K M) := sorry

/-- For a proper morphism, duality against the normalized complexes commutes with derived
pushforward on bounded-above coherent complexes, up to canonical isomorphism. -/
theorem dualizingTrace_isIsomorphic
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y)
    [IsProper f.hom.left]
    (K : D⁻[SheafOfModules.isCoherent X.obj.left.toRingedSpace.ringCatSheaf]) :
    IsIsomorphic
      ((RingedSpace.moduleDerivedPushforward f.hom.left.toShHom).obj
        ((@MonoidalClosed.ihomOf _ _ (D.monoidal X) (D.closed X) K.obj.obj).obj
          (D.omega X).obj.obj))
      ((@MonoidalClosed.ihomOf _ _ (D.monoidal Y) (D.closed Y)
        ((RingedSpace.moduleDerivedPushforward f.hom.left.toShHom).obj K.obj.obj)).obj
          (D.omega Y).obj.obj) := sorry

end AlgebraicGeometry.Scheme.NewUpperShriekAssignment

namespace AlgebraicGeometry.Scheme.NewUpperShriekAssignment

variable {S : Scheme.{u}} [IsNoetherian S]
variable [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
variable {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
variable {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}

/-- On a finite-type separated `S`-scheme, the normalized complex agrees objectwise with
the earlier compactification-based upper shriek of the normalized base complex. -/
theorem omega_isIsomorphic_upperShriek
    (D : NewUpperShriekAssignment S H ωS hωS) (E : UpperShriekAssignment S)
    (X : FiniteTypeSeparatedOver S) :
    IsIsomorphic (D.omega (FiniteTypeSeparatedOver.toFiniteTypeOver X)).obj.obj
      ((E.map (FiniteTypeSeparatedOver.toBase X)).obj
        ((DerivedQCoh.coherentPlusInclusion S).obj
          (D.omega (FiniteTypeOver.base S)))).obj.obj := sorry

/-- On finite-type separated `S`-schemes, new upper shriek and the earlier
compactification-based upper shriek agree objectwise. No compatibility with composition
comparisons is asserted. -/
theorem map_obj_isIsomorphic_upperShriek
    (D : NewUpperShriekAssignment S H ωS hωS) (E : UpperShriekAssignment S)
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (K : D⁺[SheafOfModules.isCoherent Y.obj.left.toRingedSpace.ringCatSheaf]) :
    IsIsomorphic
      ((D.map (FiniteTypeSeparatedOver.homToFiniteTypeOver f)).obj K).obj.obj
      ((E.map f).obj ((DerivedQCoh.coherentPlusInclusion Y.obj.left).obj K)).obj.obj := sorry

end AlgebraicGeometry.Scheme.NewUpperShriekAssignment
