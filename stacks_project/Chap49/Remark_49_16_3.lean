module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Different
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.FiniteFlatTrace
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different.GenericEtale
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory SheafOfModules
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

/- Remark 49.16.3 (1): for a quasi-finite Gorenstein morphism `f : Y ⟶ X` of
compactifyable Cohen–Macaulay schemes over a Noetherian scheme with dualizing complex,
generically étale on `Y`, one has
`ωY ≅ f⁺*ωX ⊗ O_Y(W.different τ)`. -/
@[stacks 0C18]
#check (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.dualizingModule_isIsomorphic_pullbackTensorDifferent :
    ∀ {S : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsNoetherian S]
      [MonoidalCategory (AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace)]
      {H : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace)}
      {ωS : AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace}
      {hωS : ωS.IsDualizingComplex H}
      (D : AlgebraicGeometry.Scheme.NewUpperShriekAssignment S H ωS hωS)
      {X Y : AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S} (f : Y ⟶ X)
      [AlgebraicGeometry.Scheme.Hom.QuasiFinite f.hom.left]
      [AlgebraicGeometry.Gorenstein f.hom.left]
      [AlgebraicGeometry.Scheme.CohenMacaulay X.obj.left]
      [AlgebraicGeometry.Scheme.CohenMacaulay Y.obj.left]
      (ωX : AlgebraicGeometry.Scheme.Modules X.obj.left)
      (ωY : AlgebraicGeometry.Scheme.Modules Y.obj.left)
      (dX : LocallyConstant X.obj.left ℕ) (dY : LocallyConstant Y.obj.left ℕ)
      (hX : IsLocallyShiftedSingle
        (D.omega (AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.toFiniteTypeOver X)).obj.obj ωX dX)
      (hY : IsLocallyShiftedSingle
        (D.omega (AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.toFiniteTypeOver Y)).obj.obj ωY dY)
      (W : AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf f.hom.left)
      (hW : W.module.obj =
        D.dualizingModule (AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.homToFiniteTypeOver f))
      (τ : SheafOfModules.sections W.module.obj) (hτ : W.IsTraceSection τ)
      (h_generic : ∀ y : Y.obj.left,
        y ∈ genericPoints Y.obj.left → AlgebraicGeometry.Scheme.Hom.EtaleAt f.hom.left y),
      ∃ hR : IsEffectiveCartierDivisor (W.different τ).subschemeι,
        IsIsomorphic ωY
          ((AlgebraicGeometry.Scheme.Modules.pullback f.hom.left).obj ωX ⊗
            @AlgebraicGeometry.Scheme.IdealSheafData.associatedSheaf
              Y.obj.left (W.different τ) hR))

/- Remark 49.16.3 (2): for finite `f`, the trace section defining the different
corresponds under duality to the finite-flat trace map. -/
@[stacks 0C18]
#check (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.traceSection_eq_adjointTrace :
    ∀ {X Y : AlgebraicGeometry.Scheme} (f : Y ⟶ X)
      [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
      [IsFinite f] [Flat f]
      (W : f.RelativeDualizingSheaf)
      (hW : AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologySheaf
        ((AlgebraicGeometry.Scheme.DerivedQCoh.finiteRightAdjoint f).obj
          (AlgebraicGeometry.Scheme.DerivedQCoh.structureSheaf X)).obj 0 = W.module.obj)
      (τ : W.module.obj.sections) (hτ : W.IsTraceSection τ),
      SheafOfModules.sectionsMap (eqToIso hW).hom
        (AlgebraicGeometry.Scheme.DerivedQCoh.adjointTraceSection f W hW) = τ)
