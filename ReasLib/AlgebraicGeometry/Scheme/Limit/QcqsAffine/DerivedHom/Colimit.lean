/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine.DerivedHom
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

public section

/-!
# Filtered colimits of derived Hom types for qcqs affine limits

This module gives the colimit theorem for the canonical derived Hom diagram of direct
pullbacks from a distinguished stage of a qcqs affine limit.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit.DerivedHom

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {D : OrderDual I ⥤ Scheme.{u}}
variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/-- For a directed inverse limit of qcqs schemes with affine transition maps, the canonical
cocone of direct-stage derived Hom types is colimiting when the target has quasi-coherent
cohomology and either the source is perfect or the source is pseudo-coherent while the target
has finite Tor dimension. -/
theorem diagram_isColimit
    (s : Scheme.Limit.QcqsAffineLimit D)
    (E₀ K₀ : RingedSpace.ModuleDerived
      (D.obj (OrderDual.toDual s.base)).toRingedSpace)
    (hK₀qc : DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty
        (D.obj (OrderDual.toDual s.base)).toRingedSpace) K₀)
    (h_finite : RingedSpace.ModuleDerived.IsPerfect E₀ ∨
      (RingedSpace.ModuleDerived.IsPseudoCoherent E₀ ∧
        RingedSpace.HasFiniteTorDimension K₀)) :
    Nonempty (IsColimit (diagram s E₀ K₀).cocone) := sorry

end AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit.DerivedHom
