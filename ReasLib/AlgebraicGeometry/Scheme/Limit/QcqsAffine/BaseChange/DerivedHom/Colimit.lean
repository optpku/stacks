/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local
public import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine.BaseChange.DerivedHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Operations

public section

/-!
# Filtered colimits of derived Hom types after base change

This module gives the colimit theorem for the canonical derived Hom diagram associated to a
flat, finitely presented base change of a qcqs affine limit.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {D : OrderDual I ⥤ Scheme.{u}}
variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/-- For a flat finitely presented base change of a qcqs affine limit, the canonical cocone of
derived Hom types is colimiting when the source is pseudo-coherent and the target has
quasi-coherent cohomology and locally finite Tor dimension relative to the base. -/
theorem homDiagram_isColimit_exists
    (s : QcqsAffineLimit D) (X₀ : Scheme.{u})
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    [Flat x₀] [Scheme.Hom.FinitePresentation x₀]
    (K₀ L₀ : RingedSpace.ModuleDerived X₀.toRingedSpace)
    (hK₀ : RingedSpace.ModuleDerived.IsPseudoCoherent K₀)
    (hL₀qc : DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X₀.toRingedSpace) L₀)
    (hL₀tor : RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
      ((RingedSpace.ModuleDerived.relativeRestriction x₀.toLRSHom.toShHom).obj L₀)) :
    Nonempty (IsColimit (s.homDiagram x₀ K₀ L₀).cocone) := sorry

end AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit
