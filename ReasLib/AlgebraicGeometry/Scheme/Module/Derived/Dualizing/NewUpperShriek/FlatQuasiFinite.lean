/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.TorAmplitude
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry.Scheme.NewUpperShriekAssignment

variable {S : Scheme.{u}} [IsNoetherian S]
variable [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
variable {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
variable {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}

/-- The degree-zero dualizing module of a flat quasi-finite morphism is coherent. -/
theorem dualizingModule_isCoherent
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y)
    [Flat f.hom.left] [Scheme.Hom.QuasiFinite f.hom.left] :
    (D.dualizingModule f).IsCoherent := sorry

/-- The degree-zero dualizing module of a flat quasi-finite morphism is flat over
the target. -/
theorem dualizingModule_isFlatOver
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y)
    [Flat f.hom.left] [Scheme.Hom.QuasiFinite f.hom.left] :
    SheafOfModules.IsFlatOver (D.dualizingModule f) (f.hom.left).toShHom := sorry

/-- The new-upper-shriek dualizing object of a flat quasi-finite morphism is its
degree-zero dualizing module placed in degree zero. -/
theorem dualizingObject_isomorphic_single_dualizingModule
    (D : NewUpperShriekAssignment S H ωS hωS)
    {X Y : FiniteTypeOver S} (f : X ⟶ Y)
    [Flat f.hom.left] [Scheme.Hom.QuasiFinite f.hom.left] :
    IsIsomorphic (D.dualizingObject f)
      ((DerivedCategory.singleFunctor (X.obj.left).Modules 0).obj (D.dualizingModule f)) := sorry

end AlgebraicGeometry.Scheme.NewUpperShriekAssignment
