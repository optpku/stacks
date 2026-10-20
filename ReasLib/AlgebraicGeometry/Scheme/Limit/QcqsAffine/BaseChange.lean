module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine
public import ReasLib.AlgebraicGeometry.Scheme.Limit.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/-- The canonical cone obtained by base changing a specified qcqs affine-transition limit
along a flat morphism of finite presentation into its distinguished stage. -/
noncomputable def flatFinitePresentationBaseChangeCone
    (s : QcqsAffineLimit D) (X₀ : Scheme.{u})
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
    [Flat x₀] [Scheme.Hom.FinitePresentation x₀] :
    Cone (Scheme.baseChangeOverDiagram D (OrderDual.toDual s.base) x₀) :=
  Scheme.baseChangeOverCone D s.limitCone.cone (OrderDual.toDual s.base) x₀

end AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit
