/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.CohenMacaulay
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived

universe u

namespace AlgebraicGeometry.Scheme.NewUpperShriekAssignment

/- Remark 48.21.8 (1): the fibre-dimension lower bound for new upper shriek. -/
@[stacks 0BV9] #check
  (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.neg_fiberDimension_le_of_cohomologyStalk_nontrivial :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
      {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
      (D : NewUpperShriekAssignment S H ωS hωS)
      {X Y : FiniteTypeOver S} (f : X ⟶ Y) (x : X.obj.left) (d : ℕ),
      fiberDimensionAt f.hom.left x = (d : WithBot ℕ∞) → ∀ i : ℤ,
      Nontrivial (cohomologyStalk (D.dualizingObject f) i x) → -(d : ℤ) ≤ i)

/- Remark 48.21.8 (2): the cohomology-stalk degree range for flat morphisms. -/
@[stacks 0BV9] #check
  (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.cohomologyStalk_degree_mem_of_flat :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
      {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
      (D : NewUpperShriekAssignment S H ωS hωS)
      {X Y : FiniteTypeOver S} (f : X ⟶ Y) [Flat f.hom.left]
      (x : X.obj.left) (d : ℕ),
      fiberDimensionAt f.hom.left x = (d : WithBot ℕ∞) → ∀ i : ℤ,
      Nontrivial (cohomologyStalk (D.dualizingObject f) i x) →
        i ∈ Set.Icc (-(d : ℤ)) 0)

/- Remark 48.21.8 (3): the relative Tor-amplitude bound for flat morphisms. -/
@[stacks 0BV9] #check
  ((by
    intro S _ _ H ωS hωS D X Y f _ d _
    exact D.dualizingObject_hasTorAmplitudeInOver_of_flat f d) :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
      {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
      (D : NewUpperShriekAssignment S H ωS hωS)
      {X Y : FiniteTypeOver S} (f : X ⟶ Y) [Flat f.hom.left]
      (d : ℕ) [Scheme.Hom.RelativeDimensionLE f.hom.left d],
      HasTorAmplitudeInOver (f.hom.left).toShHom
        (D.dualizingObject f) (-(d : ℤ)) 0)

/- Remark 48.21.8 (4): coherence of the dualizing module for flat quasi-finite morphisms. -/
@[stacks 0BV9] #check
  (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.dualizingModule_isCoherent :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
      {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
      (D : NewUpperShriekAssignment S H ωS hωS)
      {X Y : FiniteTypeOver S} (f : X ⟶ Y)
      [Flat f.hom.left] [Scheme.Hom.QuasiFinite f.hom.left],
      (D.dualizingModule f).IsCoherent)

/- Remark 48.21.8 (5): relative flatness of the dualizing module for flat quasi-finite morphisms. -/
@[stacks 0BV9] #check
  (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.dualizingModule_isFlatOver :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
      {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
      (D : NewUpperShriekAssignment S H ωS hωS)
      {X Y : FiniteTypeOver S} (f : X ⟶ Y)
      [Flat f.hom.left] [Scheme.Hom.QuasiFinite f.hom.left],
      SheafOfModules.IsFlatOver (D.dualizingModule f) (f.hom.left).toShHom)

/- Remark 48.21.8 (6): the degree-zero description for flat quasi-finite morphisms. -/
@[stacks 0BV9] #check
  (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.dualizingObject_isomorphic_single_dualizingModule :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
      {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
      (D : NewUpperShriekAssignment S H ωS hωS)
      {X Y : FiniteTypeOver S} (f : X ⟶ Y)
      [Flat f.hom.left] [Scheme.Hom.QuasiFinite f.hom.left],
      IsIsomorphic (D.dualizingObject f)
        ((DerivedCategory.singleFunctor (X.obj.left).Modules 0).obj (D.dualizingModule f)))

/- Remark 48.21.8 (7): the locally shifted dualizing-module description for
Cohen-Macaulay morphisms. -/
@[stacks 0BV9] #check
  (AlgebraicGeometry.Scheme.NewUpperShriekAssignment.exists_dualizingModule_of_cohenMacaulay :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      {H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)}
      {ωS : RingedSpace.ModuleDerived S.toRingedSpace} {hωS : ωS.IsDualizingComplex H}
      (D : NewUpperShriekAssignment S H ωS hωS)
      {X Y : FiniteTypeOver S} (f : X ⟶ Y)
      [AlgebraicGeometry.CohenMacaulay f.hom.left],
      ∃ d : LocallyConstant X.obj.left ℕ, ∃ ω : (X.obj.left).Modules,
        (∀ x : X.obj.left, fiberDimensionAt f.hom.left x = (d x : WithBot ℕ∞)) ∧
        ω.IsCoherent ∧ SheafOfModules.IsFlatOver ω (f.hom.left).toShHom ∧
        IsLocallyShiftedSingle (D.dualizingObject f) ω d)

end AlgebraicGeometry.Scheme.NewUpperShriekAssignment
