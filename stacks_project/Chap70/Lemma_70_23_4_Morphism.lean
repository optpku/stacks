module

public import Mathlib.CategoryTheory.Category.Preorder
public import stacks_project.Chap70.Lemma_70_23_3_BaseChange

/-!
# Morphisms of inverse systems of algebraic spaces over a tail of the base

This leaf records the tail of a directed base diagram of algebraic spaces, the
restriction of a stagewise system to a later tail, and morphisms of such systems
over the base.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The base inverse system restricted to stages `j ≥ i0`. -/
abbrev tailBaseDiagram {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (i0 : I) :
    Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S :=
  Over.forget (OrderDual.toDual i0) ⋙ D

/-- The object of the tail category represented by a stage `j ≥ i0`. -/
abbrev tailObject {I : Type u} [Preorder I] {i0 : I} (j : I) (h : i0 ≤ j) :
    Over (OrderDual.toDual i0) :=
  Over.mk (homOfLE h : OrderDual.toDual j ⟶ OrderDual.toDual i0)

/-- Restrict an inverse system starting at `i` to a later tail starting at `i0`. -/
abbrev restrictTail {I : Type u} [Preorder I] {S : Scheme.{u}}
    {i i0 : I} (h : i ≤ i0)
    (Xsys : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S) :
    Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S :=
  Over.map (homOfLE h : OrderDual.toDual i0 ⟶ OrderDual.toDual i) ⋙ Xsys

/-- Restrict the structural map from an inverse system to the base system to a later tail. -/
abbrev restrictTailToBase {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) {i i0 : I} (h : i ≤ i0)
    {Xsys : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S}
    (xToBase : Xsys ⟶ tailBaseDiagram D i) :
    restrictTail h Xsys ⟶ tailBaseDiagram D i0 :=
  Functor.whiskerLeft
    (Over.map (homOfLE h : OrderDual.toDual i0 ⟶ OrderDual.toDual i)) xToBase

/-- The natural transformation from a stagewise fibre-product diagram
`T ×_{B_{i0}} B_j` to the tail of the base diagram, with components the first
projections. -/
def baseChangeOverToTail {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (i0 : I) {T : AlgebraicSpace S}
    (t : T ⟶ D.obj (OrderDual.toDual i0)) :
    baseChangeOverDiagram D (OrderDual.toDual i0) t ⟶ tailBaseDiagram D i0 where
  app j := pullback.fst (D.map j.hom) t
  naturality := sorry

/-- Components of `baseChangeOverToTail` are the first projections of the
stagewise fibre products. -/
theorem baseChangeOverToTail_app {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (i0 : I) {T : AlgebraicSpace S}
    (t : T ⟶ D.obj (OrderDual.toDual i0)) (j : Over (OrderDual.toDual i0)) :
    (baseChangeOverToTail D i0 t).app j = pullback.fst (D.map j.hom) t :=
  sorry

/-- A morphism of inverse systems over the same tail of the base system. -/
abbrev InverseSystemMorphismOverBase {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (i0 : I)
    (Xsys Ysys : Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S)
    (xToBase : Xsys ⟶ tailBaseDiagram D i0)
    (yToBase : Ysys ⟶ tailBaseDiagram D i0) :=
  (Over.mk xToBase : Over (tailBaseDiagram D i0)) ⟶ Over.mk yToBase

namespace InverseSystemMorphismOverBase

/-- The underlying natural transformation of a morphism of inverse systems over a base. -/
abbrev hom {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
    {Xsys Ysys : Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0}
    {yToBase : Ysys ⟶ tailBaseDiagram D i0}
    (φ : InverseSystemMorphismOverBase D i0 Xsys Ysys xToBase yToBase) :
    Xsys ⟶ Ysys :=
  φ.left

/-- The underlying natural transformation of a morphism over a base commutes with the
structural maps. -/
theorem over_base {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
    {Xsys Ysys : Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0}
    {yToBase : Ysys ⟶ tailBaseDiagram D i0}
    (φ : InverseSystemMorphismOverBase D i0 Xsys Ysys xToBase yToBase) :
    φ.hom ≫ yToBase = xToBase :=
  sorry

/-- The identity morphism of an inverse system over a base. -/
def id {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
    {Xsys : Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0} :
    InverseSystemMorphismOverBase D i0 Xsys Xsys xToBase xToBase :=
  𝟙 (Over.mk xToBase)

/-- Composition of morphisms of inverse systems over a common base. -/
def comp {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
    {Xsys Ysys Zsys : Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0}
    {yToBase : Ysys ⟶ tailBaseDiagram D i0}
    {zToBase : Zsys ⟶ tailBaseDiagram D i0}
    (φ : InverseSystemMorphismOverBase D i0 Xsys Ysys xToBase yToBase)
    (ψ : InverseSystemMorphismOverBase D i0 Ysys Zsys yToBase zToBase) :
    InverseSystemMorphismOverBase D i0 Xsys Zsys xToBase zToBase :=
  φ ≫ ψ

/-- A morphism of inverse systems induces the specified morphism on the limit cones. -/
def IsLimitMorphism {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
    {Xsys Ysys : Over (OrderDual.toDual i0) ⥤ AlgebraicSpace S}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0}
    {yToBase : Ysys ⟶ tailBaseDiagram D i0}
    (φ : InverseSystemMorphismOverBase D i0 Xsys Ysys xToBase yToBase)
    (xCone : Cone Xsys) (yCone : Cone Ysys) (f : xCone.pt ⟶ yCone.pt) : Prop :=
  ∀ j : Over (OrderDual.toDual i0),
    f ≫ yCone.π.app j = xCone.π.app j ≫ φ.hom.app j

end InverseSystemMorphismOverBase

end AlgebraicGeometry.AlgebraicSpace
