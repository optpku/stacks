module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffine.DerivedHom

public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.DerivedHom

noncomputable section

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]


/- The canonical derived Hom diagram for the cofinal tail of a specified qcqs affine limit. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.DerivedHom.diagram :
    ∀ (s : AlgebraicSpace.Limit.QcqsAffineLimit D)
      (E₀ K₀ : ModuleDerived (D.obj (OrderDual.toDual s.base))),
      DerivedCategory.FilteredColimit.HomDiagram (stageFunctor s E₀ K₀)
        ((limitPullback s).obj E₀ ⟶ (limitPullback s).obj K₀))
