module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.FieldExtension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent

/-!
# Euler characteristics under field extension

This leaf records invariance of Euler characteristics under extension of the ground field.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The Euler characteristic of a coherent module on a proper scheme over a field is unchanged
after extending the ground field. -/
@[stacks 08AB]
theorem eulerCharacteristic_baseChange_of_fieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    eulerCharacteristic f ℱ =
      eulerCharacteristic
        (FieldExtension.toBase k K f)
        (Scheme.Modules.FieldExtension.baseChange k K f ℱ) := sorry

end AlgebraicGeometry.Scheme.Hom
