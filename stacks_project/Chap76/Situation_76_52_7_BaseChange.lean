module

public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap70.Lemma_70_23_3_BaseChange
public import stacks_project.Chap70.Situation_70_5_5_QcqsAffine

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- The canonical cone obtained by base changing a specified qcqs affine-transition
limit of algebraic spaces along a flat morphism of finite presentation into its
distinguished stage. -/
noncomputable def flatFinitePresentationBaseChangeCone
    (s : QcqsAffineLimit D) (X₀ : AlgebraicSpace S)
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    [Flat x₀] [FinitePresentation x₀] :
    Cone (baseChangeOverDiagram D (OrderDual.toDual s.base) x₀) :=
  baseChangeOverCone D s.limitCone.cone (OrderDual.toDual s.base) x₀

/-- `flatFinitePresentationBaseChangeCone` agrees with the Over-indexed base-change
cone of the specified limit along `x₀`. -/
theorem flatFinitePresentationBaseChangeCone_eq
    (s : QcqsAffineLimit D) (X₀ : AlgebraicSpace S)
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    [Flat x₀] [FinitePresentation x₀] :
    flatFinitePresentationBaseChangeCone D s X₀ x₀ =
      baseChangeOverCone D s.limitCone.cone (OrderDual.toDual s.base) x₀ :=
  sorry

/-- The vertex of `flatFinitePresentationBaseChangeCone` is the fibre product of the
limit projection at the distinguished stage with `x₀`. -/
theorem flatFinitePresentationBaseChangeCone_pt
    (s : QcqsAffineLimit D) (X₀ : AlgebraicSpace S)
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    [Flat x₀] [FinitePresentation x₀] :
    (flatFinitePresentationBaseChangeCone D s X₀ x₀).pt =
      pullback (s.limitCone.cone.π.app (OrderDual.toDual s.base)) x₀ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit

