/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.tailBaseDiagram :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (i0 : I),
    Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.tailObject :
  ∀ {I : Type u} [Preorder I] {i0 : I} (j : I) (h : i0 ≤ j),
    Over (OrderDual.toDual i0))

#check (AlgebraicGeometry.AlgebraicSpace.restrictTail :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    {i i0 : I} (h : i ≤ i0)
    (Xsys : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S),
    Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.restrictTailToBase :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) {i i0 : I} (h : i ≤ i0)
    {Xsys : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S}
    (xToBase : Xsys ⟶ tailBaseDiagram D i),
    restrictTail h Xsys ⟶ tailBaseDiagram D i0)

#check (AlgebraicGeometry.AlgebraicSpace.baseChangeOverToTail :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (i0 : I) {T : AlgebraicSpace S}
    (t : T ⟶ D.obj (OrderDual.toDual i0)),
    baseChangeOverDiagram D (OrderDual.toDual i0) t ⟶ tailBaseDiagram D i0)

#check (AlgebraicGeometry.AlgebraicSpace.baseChangeOverToTail_app :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (i0 : I) {T : AlgebraicSpace S}
    (t : T ⟶ D.obj (OrderDual.toDual i0)) (j : Over (OrderDual.toDual i0)),
    (baseChangeOverToTail D i0 t).app j = pullback.fst (D.map j.hom) t)

#check (AlgebraicGeometry.AlgebraicSpace.InverseSystemMorphismOverBase :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (i0 : I)
    (Xsys Ysys : Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S)
    (xToBase : Xsys ⟶ tailBaseDiagram D i0)
    (yToBase : Ysys ⟶ tailBaseDiagram D i0),
    Type (u + 1))

namespace InverseSystemMorphismOverBase

#check (AlgebraicGeometry.AlgebraicSpace.InverseSystemMorphismOverBase.hom :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
    {Xsys Ysys : Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0}
    {yToBase : Ysys ⟶ tailBaseDiagram D i0}
    (φ : InverseSystemMorphismOverBase D i0 Xsys Ysys xToBase yToBase),
    Xsys ⟶ Ysys)

#check (AlgebraicGeometry.AlgebraicSpace.InverseSystemMorphismOverBase.over_base :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
    {Xsys Ysys : Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0}
    {yToBase : Ysys ⟶ tailBaseDiagram D i0}
    (φ : InverseSystemMorphismOverBase D i0 Xsys Ysys xToBase yToBase),
    φ.hom ≫ yToBase = xToBase)

#check (AlgebraicGeometry.AlgebraicSpace.InverseSystemMorphismOverBase.id :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
    {Xsys : Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0},
    InverseSystemMorphismOverBase D i0 Xsys Xsys xToBase xToBase)

#check (AlgebraicGeometry.AlgebraicSpace.InverseSystemMorphismOverBase.comp :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
    {Xsys Ysys Zsys : Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0}
    {yToBase : Ysys ⟶ tailBaseDiagram D i0}
    {zToBase : Zsys ⟶ tailBaseDiagram D i0}
    (φ : InverseSystemMorphismOverBase D i0 Xsys Ysys xToBase yToBase)
    (ψ : InverseSystemMorphismOverBase D i0 Ysys Zsys yToBase zToBase),
    InverseSystemMorphismOverBase D i0 Xsys Zsys xToBase zToBase)

#check (AlgebraicGeometry.AlgebraicSpace.InverseSystemMorphismOverBase.IsLimitMorphism :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
    {Xsys Ysys : Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0}
    {yToBase : Ysys ⟶ tailBaseDiagram D i0}
    (φ : InverseSystemMorphismOverBase D i0 Xsys Ysys xToBase yToBase)
    (xCone : Cone Xsys) (yCone : Cone Ysys) (f : xCone.pt ⟶ yCone.pt),
    Prop)

end InverseSystemMorphismOverBase

end AlgebraicGeometry.AlgebraicSpace
