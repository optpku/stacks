/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RightAdjoint
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure

/-!
# Exactness of quasicoherent coreflections on algebraic spaces

The right adjoint to the inclusion of derived modules with quasi-coherent
cohomology carries the adjunction-induced shift comparison and is triangulated.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The chosen right adjoint of the inclusion of derived modules with quasi-coherent
cohomology carries the canonical shift comparison induced by its adjunction. -/
noncomputable instance instCommShift_inclusion_rightAdjoint {S : Scheme.{u}}
    (X : AlgebraicSpace S) [(inclusion X).IsLeftAdjoint] :
    ((inclusion X).rightAdjoint).CommShift ℤ :=
  (Adjunction.ofIsLeftAdjoint (inclusion X)).rightAdjointCommShift ℤ

/-- The inclusion–coreflection adjunction is compatible with its canonical shift
comparisons. -/
instance instCommShift_inclusion_adjunction {S : Scheme.{u}}
    (X : AlgebraicSpace S) [(inclusion X).IsLeftAdjoint] :
    (Adjunction.ofIsLeftAdjoint (inclusion X)).CommShift ℤ :=
  (Adjunction.ofIsLeftAdjoint (inclusion X)).commShift_of_leftAdjoint ℤ

/-- The chosen right adjoint of the inclusion of derived modules with quasi-coherent
cohomology is a triangulated functor. -/
instance instIsTriangulated_inclusion_rightAdjoint {S : Scheme.{u}}
    (X : AlgebraicSpace S) [(inclusion X).IsLeftAdjoint] :
    ((inclusion X).rightAdjoint).IsTriangulated :=
  (Adjunction.ofIsLeftAdjoint (inclusion X)).isTriangulated_rightAdjoint

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
