/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_5_6_Instances
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_24_2_DerivedHom

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
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- For a directed inverse limit of qcqs algebraic spaces with affine transition maps, the
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
    Nonempty (IsColimit (diagram s E₀ K₀).cocone) :=
  sorry

/-- The Hom diagram is colimiting when the source is perfect and the target has
quasi-coherent cohomology. -/
theorem diagram_isColimit_of_isPerfect
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    (hE₀ : ModuleDerived.IsPerfect E₀)
    (hK₀qc : derivedQuasiCoherentModuleProperty
      (D.obj (OrderDual.toDual s.base)) K₀) :
    Nonempty (IsColimit (diagram s E₀ K₀).cocone) :=
  sorry

/-- The Hom diagram is colimiting when the source is pseudo-coherent and the target has
quasi-coherent cohomology and finite Tor dimension. -/
theorem diagram_isColimit_of_isPseudoCoherent
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
    (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base)))
    (hE₀ : IsPseudoCoherent (D.obj (OrderDual.toDual s.base)) E₀)
    (hK₀qc : derivedQuasiCoherentModuleProperty
      (D.obj (OrderDual.toDual s.base)) K₀)
    (hK₀tor : DerivedCategory.DerivedTensor.HasFiniteTorDimension K₀) :
    Nonempty (IsColimit (diagram s E₀ K₀).cocone) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.DerivedHom
