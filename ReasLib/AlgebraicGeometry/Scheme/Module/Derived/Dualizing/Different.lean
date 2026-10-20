module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.Assignment
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.Dualizing
public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.Base
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different.GenericEtale

@[expose] public section

open AlgebraicGeometry CategoryTheory SheafOfModules
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace NewUpperShriekAssignment

/-- The degree-zero absolute dualizing modules of a Cohen–Macaulay morphism of relative
dimension zero are related by pullback and tensor product with its relative dualizing
module. -/
theorem dualizingModule_isIsomorphic_pullbackTensorRelative
    {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : Y ⟶ X)
    [AlgebraicGeometry.CohenMacaulay f.hom.left]
    [Scheme.Hom.RelativeDimension f.hom.left 0]
    [Scheme.Hom.QuasiFinite f.hom.left]
    [Scheme.CohenMacaulay X.obj.left] [Scheme.CohenMacaulay Y.obj.left]
    (ωX : Modules X.obj.left) (ωY : Modules Y.obj.left)
    (dX : LocallyConstant X.obj.left ℕ) (dY : LocallyConstant Y.obj.left ℕ)
    (hX : IsLocallyShiftedSingle (D.omega X).obj.obj ωX dX)
    (hY : IsLocallyShiftedSingle (D.omega Y).obj.obj ωY dY)
    (W : RelativeDualizingSheaf f.hom.left)
    (hW : W.module.obj = D.dualizingModule f) :
    IsIsomorphic ωY
      ((Modules.pullback f.hom.left).obj ωX ⊗ W.module.obj) := sorry

/-- A quasi-finite Gorenstein generically étale morphism between Cohen–Macaulay
finite-type-separated schemes has a dualizing-module comparison through its different. -/
theorem dualizingModule_isIsomorphic_pullbackTensorDifferent
    {S : Scheme.{u}} [IsNoetherian S]
    [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
    {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
    {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeSeparatedOver S} (f : Y ⟶ X)
    [Scheme.Hom.QuasiFinite f.hom.left]
    [AlgebraicGeometry.Gorenstein f.hom.left]
    [Scheme.CohenMacaulay X.obj.left] [Scheme.CohenMacaulay Y.obj.left]
    (ωX : Modules X.obj.left) (ωY : Modules Y.obj.left)
    (dX : LocallyConstant X.obj.left ℕ) (dY : LocallyConstant Y.obj.left ℕ)
    (hX : IsLocallyShiftedSingle
      (D.omega (FiniteTypeSeparatedOver.toFiniteTypeOver X)).obj.obj ωX dX)
    (hY : IsLocallyShiftedSingle
      (D.omega (FiniteTypeSeparatedOver.toFiniteTypeOver Y)).obj.obj ωY dY)
    (W : RelativeDualizingSheaf f.hom.left)
    (hW : W.module.obj =
      D.dualizingModule (FiniteTypeSeparatedOver.homToFiniteTypeOver f))
    (τ : sections W.module.obj) (hτ : W.IsTraceSection τ)
    (h_generic : ∀ y : Y.obj.left,
      y ∈ genericPoints Y.obj.left → Hom.EtaleAt f.hom.left y) :
    ∃ hR : IsEffectiveCartierDivisor (W.different τ).subschemeι,
      IsIsomorphic ωY
        ((Modules.pullback f.hom.left).obj ωX ⊗
          @IdealSheafData.associatedSheaf Y.obj.left (W.different τ) hR) := sorry

end NewUpperShriekAssignment
end Scheme
end AlgebraicGeometry
