module

import StacksCheckRecall
import stacks_project.Chap48.Lemma_48_20_9_Comparison
import stacks_project.Chap48.Lemma_48_20_9_Pseudofunctor

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory Opposite
open scoped CategoryTheory.Bicategory DerivedCategory.CohomologyIn

universe u

/- Lemma 48.20.9 (1): the new upper-shriek functors and composition maps form a pseudofunctor. -/
@[stacks 0AUE] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.pseudofunctor :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H},
    NewUpperShriekAssignment S H ωS hωS → LocallyDiscrete (FiniteTypeOver S)ᵒᵖ ⥤ᵖ Cat)

/- Lemma 48.20.9 (2): the normalized complex is new upper shriek from the base. -/
@[stacks 0AUE] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.omega_isIsomorphic_mapToBase :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) (X : FiniteTypeOver S),
    IsIsomorphic (D.omega X) ((D.map (FiniteTypeOver.toBase X)).obj
      (D.omega (FiniteTypeOver.base S))))

/- Lemma 48.20.9 (3): coherent duality is involutive. -/
@[stacks 0AUE] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.coherentDualityInvolutive :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) (X : FiniteTypeOver S),
    IsIso (@Scheme.IsDualizingComplex.coherentBidual X.obj.left inferInstance
      (D.monoidal X) (D.braided X) (D.closed X) (D.omega X).obj.obj
      (D.dualizing X)))

/- Lemma 48.20.9 (4): duality exchanges bounded-below and bounded-above coherent complexes. -/
@[stacks 0AUE] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.plusDualityIsEquivalence :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) (X : FiniteTypeOver S),
    (@Scheme.IsDualizingComplex.plusDuality X.obj.left inferInstance
      (D.monoidal X) (D.braided X) (D.closed X) (D.omega X).obj.obj
      (D.dualizing X) inferInstance).IsEquivalence)

/- Lemma 48.20.9 (5): duality preserves bounded coherent complexes. -/
@[stacks 0AUE] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.boundedDualityIsEquivalence :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) (X : FiniteTypeOver S),
    (@Scheme.IsDualizingComplex.boundedDuality X.obj.left inferInstance
      (D.monoidal X) (D.braided X) (D.closed X) (D.omega X).obj.obj
      (D.dualizing X) inferInstance).IsEquivalence)

/- Lemma 48.20.9 (6): normalized complexes are functorial under new upper shriek. -/
@[stacks 0AUE] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.omega_isIsomorphic_map :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) {X Y : FiniteTypeOver S} (f : X ⟶ Y),
    IsIsomorphic (D.omega X) ((D.map f).obj (D.omega Y)))

/- Lemma 48.20.9 (7): new upper shriek is duality-pullback-duality objectwise. -/
@[stacks 0AUE] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.map_obj_obj :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) {X Y : FiniteTypeOver S} (f : X ⟶ Y)
    (K : DerivedCoh.Plus Y.obj.left),
    ((D.map f).obj K).obj.obj =
      (@MonoidalClosed.ihomOf _ _ (D.monoidal X) (D.closed X)
        ((RingedSpace.modulePullbackDerived f.hom.left.toShHom).obj
          ((@MonoidalClosed.ihomOf _ _ (D.monoidal Y) (D.closed Y) K.obj.obj).obj
            (D.omega Y).obj.obj))).obj (D.omega X).obj.obj)

/- Lemma 48.20.9 (8): proper new upper shriek restricts a right adjoint. -/
@[stacks 0AUE] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.properRestriction_isIsomorphic :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) {X Y : FiniteTypeOver S} (f : X ⟶ Y)
    [IsProper f.hom.left] (A : DerivedQCoh.PlusRightAdjoint f.hom.left),
    IsIsomorphic (D.map f)
      (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.properRestriction f A))

/- Lemma 48.20.9 (9): the proper trace map is invertible. -/
@[stacks 0AUE] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.properTraceMap_isIso :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) {X Y : FiniteTypeOver S} (f : X ⟶ Y)
    [IsProper f.hom.left]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.hom.left.toShHom)]
    [pullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _ (D.monoidal Y)
      (RingedSpace.ModuleDerived X.obj.left.toRingedSpace) _ (D.monoidal X)
      (RingedSpace.modulePullbackDerived f.hom.left.toShHom)]
    (A : DerivedQCoh.PlusRightAdjoint f.hom.left)
    (comparison : D.map f ≅
      AlgebraicGeometry.Scheme.NewUpperShriekAssignment.properRestriction f A)
    (K : D⁻[SheafOfModules.isCoherent X.obj.left.toRingedSpace.ringCatSheaf])
    (M : DerivedCoh.Plus Y.obj.left),
    IsIso (D.properTraceMap f A comparison K M))

/- Lemma 48.20.9 (10): proper pushforward commutes with normalized duality. -/
@[stacks 0AUE] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.dualizingTrace_isIsomorphic :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) {X Y : FiniteTypeOver S} (f : X ⟶ Y)
    [IsProper f.hom.left]
    (K : D⁻[SheafOfModules.isCoherent X.obj.left.toRingedSpace.ringCatSheaf]),
    IsIsomorphic
      ((RingedSpace.moduleDerivedPushforward f.hom.left.toShHom).obj
        ((@MonoidalClosed.ihomOf _ _ (D.monoidal X) (D.closed X) K.obj.obj).obj
          (D.omega X).obj.obj))
      ((@MonoidalClosed.ihomOf _ _ (D.monoidal Y) (D.closed Y)
        ((RingedSpace.moduleDerivedPushforward f.hom.left.toShHom).obj K.obj.obj)).obj
          (D.omega Y).obj.obj))

/- Lemma 48.20.9 (11): separated normalized complexes agree with compactification upper shriek. -/
@[stacks 0AUE] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.omega_isIsomorphic_upperShriek :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) (E : UpperShriekAssignment S)
    (X : FiniteTypeSeparatedOver S),
    IsIsomorphic (D.omega (FiniteTypeSeparatedOver.toFiniteTypeOver X)).obj.obj
      ((E.map (FiniteTypeSeparatedOver.toBase X)).obj
        ((DerivedQCoh.coherentPlusInclusion S).obj
          (D.omega (FiniteTypeOver.base S)))).obj.obj)

/- Lemma 48.20.9 (12): separated new upper shriek agrees with compactification upper shriek. -/
@[stacks 0AUE] #check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.map_obj_isIsomorphic_upperShriek :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS) (E : UpperShriekAssignment S)
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (K : D⁺[SheafOfModules.isCoherent Y.obj.left.toRingedSpace.ringCatSheaf]),
    IsIsomorphic
      ((D.map (FiniteTypeSeparatedOver.homToFiniteTypeOver f)).obj K).obj.obj
      ((E.map f).obj ((DerivedQCoh.coherentPlusInclusion Y.obj.left).obj K)).obj.obj)
