module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffine.DerivedHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude

/-!
# Filtered colimits of derived Hom types for qcqs affine limits of algebraic spaces

This module gives the colimit theorem for the canonical derived Hom diagram of direct
pullbacks from a distinguished stage of a qcqs affine limit of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.DerivedHom

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsAbsolutelyQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- For a directed inverse limit of quasi-compact, absolutely quasi-separated algebraic
spaces with affine transition maps, the
canonical cocone of direct-stage derived Hom types is colimiting when the target has
quasi-coherent cohomology and either the source is perfect or the source is
pseudo-coherent while the target has finite Tor dimension. -/
theorem diagram_isColimit
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    (hK₀qc : derivedQuasiCoherentModuleProperty
      (D.obj (OrderDual.toDual s.base)) K₀)
    (h_finite : ModuleDerived.IsPerfect E₀ ∨
      (IsPseudoCoherent (D.obj (OrderDual.toDual s.base)) E₀ ∧
        DerivedCategory.DerivedTensor.HasFiniteTorDimension K₀)) :
    Nonempty (IsColimit (diagram s E₀ K₀).cocone) := sorry

/-- The Hom diagram is colimiting when the source is perfect and the target has
quasi-coherent cohomology. -/
theorem diagram_isColimit_of_isPerfect
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    (hE₀ : ModuleDerived.IsPerfect E₀)
    (hK₀qc : derivedQuasiCoherentModuleProperty
      (D.obj (OrderDual.toDual s.base)) K₀) :
    Nonempty (IsColimit (diagram s E₀ K₀).cocone) := sorry

/-- The Hom diagram is colimiting when the source is pseudo-coherent and the target has
quasi-coherent cohomology and finite Tor dimension. -/
theorem diagram_isColimit_of_isPseudoCoherent
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    (hE₀ : IsPseudoCoherent (D.obj (OrderDual.toDual s.base)) E₀)
    (hK₀qc : derivedQuasiCoherentModuleProperty
      (D.obj (OrderDual.toDual s.base)) K₀)
    (hK₀tor : DerivedCategory.DerivedTensor.HasFiniteTorDimension K₀) :
    Nonempty (IsColimit (diagram s E₀ K₀).cocone) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.DerivedHom
