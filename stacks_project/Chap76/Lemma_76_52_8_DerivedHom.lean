module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.BaseChange.DerivedHom

public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- The canonical Hom diagram for the base-changed cofinal tail and its limit. -/
#check (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.homDiagram :
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
    [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    (s : AlgebraicSpace.Limit.QcqsAffineLimit D) {X₀ : AlgebraicSpace S}
    (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base)) (K₀ L₀ : ModuleDerived X₀),
    DerivedCategory.FilteredColimit.HomDiagram (s.stageHomFunctor x₀ K₀ L₀)
      ((s.limitPullback x₀).obj K₀ ⟶ (s.limitPullback x₀).obj L₀))
