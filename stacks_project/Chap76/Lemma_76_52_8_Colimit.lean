module

public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap76.Lemma_76_52_4_Relative
public import stacks_project.Chap76.Lemma_76_52_8_DerivedHom

/-!
# Filtered colimits of derived Hom types after base change of algebraic spaces

This module gives the colimit theorem for the canonical derived Hom diagram associated to a
flat, finitely presented base change of a qcqs affine limit of algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- For a flat finitely presented base change of a qcqs affine limit of algebraic spaces, the
canonical cocone of derived Hom types is colimiting when the source is pseudo-coherent and
the target has quasi-coherent cohomology and locally finite Tor dimension relative to the
base. -/
theorem homDiagram_isColimit_exists
    (s : QcqsAffineLimit D) (X₀ : AlgebraicSpace S)
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    [Flat x₀] [FinitePresentation x₀]
    (K₀ L₀ : ModuleDerived X₀)
    (hK₀ : IsPseudoCoherent X₀ K₀)
    (hL₀qc : derivedQuasiCoherentModuleProperty X₀ L₀)
    (hL₀tor : ModuleDerived.locallyFiniteTorDimensionOver x₀ L₀) :
    Nonempty (IsColimit (s.homDiagram x₀ K₀ L₀).cocone) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit
