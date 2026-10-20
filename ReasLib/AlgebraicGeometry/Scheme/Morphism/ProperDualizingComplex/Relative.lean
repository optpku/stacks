/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex

/-- A pair of intrinsic dualizing complexes is properly normalized relative to a morphism
when the target complex is the canonical right-adjoint image of a quasi-coherent source
complex, up to isomorphism. -/
def ProperRelativeTo {S X : Scheme.{u}} [IsNoetherian S] [IsNoetherian X]
    (f : X ⟶ S) [IsProper f]
    (KS : RingedSpace.ModuleDerived S.toRingedSpace)
    (KX : RingedSpace.ModuleDerived X.toRingedSpace) : Prop :=
  Scheme.IsDualizingComplex KS ∧ Scheme.IsDualizingComplex KX ∧
    ∃ Q : Scheme.DerivedQCoh S,
      IsIsomorphic Q.obj KS ∧
        IsIsomorphic
          (((Scheme.DerivedQCoh.pushforwardCohomologyIn f).rightAdjoint.obj Q).obj) KX

/-- Proper relative normalization is equivalent to the dualizingness and right-adjoint
comparison conditions in its definition. -/
theorem properRelativeTo_iff {S X : Scheme.{u}} [IsNoetherian S] [IsNoetherian X]
    (f : X ⟶ S) [IsProper f]
    (KS : RingedSpace.ModuleDerived S.toRingedSpace)
    (KX : RingedSpace.ModuleDerived X.toRingedSpace) :
    ProperRelativeTo f KS KX ↔
      Scheme.IsDualizingComplex KS ∧ Scheme.IsDualizingComplex KX ∧
        ∃ Q : Scheme.DerivedQCoh S,
          IsIsomorphic Q.obj KS ∧
            IsIsomorphic
              (((Scheme.DerivedQCoh.pushforwardCohomologyIn f).rightAdjoint.obj Q).obj) KX := sorry

end AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex
