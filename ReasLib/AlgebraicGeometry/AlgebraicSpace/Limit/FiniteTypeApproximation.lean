/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.FiniteTypeApproximation.SchemeTheoreticImage

/-!
# Finite-type approximation morphisms of algebraic spaces

This module provides tail restrictions, morphisms over a base, and finite-type
approximation limit systems for algebraic spaces.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

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
  naturality := by
    intro j j' f
    exact pullback.lift_fst _ _ _

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

/-- A finite-type approximation system whose cone is the limit, with each stage the
scheme-theoretic image in the associated base-change system. -/
structure FiniteTypeApproximationLimitSystem {I : Type u} [Preorder I]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (i : I)
    (Xsys : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S) (xCone : Cone Xsys)
    (toS : xCone.pt ⟶ c.pt) where
  /-- The finite-type approximation diagram at the initial stage. -/
  approximation : FiniteTypeApproximationDiagram toS (c.π.app i)
  /-- The structural morphism of the approximation diagram is of finite type. -/
  finiteType_toBi : FiniteType approximation.toBi
  /-- The induced morphism to the limiting base change is a closed immersion. -/
  closedImmersion_toLimitBaseChange :
    IsClosedImmersion (pullback.lift toS approximation.toW approximation.comm.w.symm)
  /-- The stage system maps into the stagewise base-change system. -/
  toImage : Xsys ⟶
    baseChangeOverDiagram D (OrderDual.toDual i) approximation.toBi
  /-- Each stage is the scheme-theoretic image of the source in the corresponding
  base change. -/
  image : ∀ j : Over (OrderDual.toDual i),
    IsSchemeTheoreticImage
      ((approximation.baseChangeCone D c).π.app j) (xCone.π.app j) (toImage.app j)
  /-- The cone with vertex the source is the limit cone for the approximation system. -/
  isLimit : IsLimit xCone

namespace FiniteTypeApproximationLimitSystem

/-- Construct a limiting finite-type approximation system from its approximation diagram,
closed-immersion and scheme-theoretic-image data, and limiting cone. -/
def ofDiagram {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (i : I)
    (Xsys : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S) (xCone : Cone Xsys)
    (toS : xCone.pt ⟶ c.pt)
    (approximation : FiniteTypeApproximationDiagram toS (c.π.app i))
    (finiteType_toBi : FiniteType approximation.toBi)
    (closedImmersion_toLimitBaseChange :
      IsClosedImmersion (pullback.lift toS approximation.toW approximation.comm.w.symm))
    (toImage : Xsys ⟶
      baseChangeOverDiagram D (OrderDual.toDual i) approximation.toBi)
    (image : ∀ j : Over (OrderDual.toDual i),
      IsSchemeTheoreticImage
        ((approximation.baseChangeCone D c).π.app j) (xCone.π.app j) (toImage.app j))
    (isLimit : IsLimit xCone) :
    FiniteTypeApproximationLimitSystem D c i Xsys xCone toS where
  approximation := approximation
  finiteType_toBi := finiteType_toBi
  closedImmersion_toLimitBaseChange := closedImmersion_toLimitBaseChange
  toImage := toImage
  image := image
  isLimit := isLimit

/-- The explicit constructor retains the supplied approximation diagram. -/
theorem ofDiagram_approximation {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (i : I)
    (Xsys : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S) (xCone : Cone Xsys)
    (toS : xCone.pt ⟶ c.pt)
    (approximation : FiniteTypeApproximationDiagram toS (c.π.app i))
    (finiteType_toBi : FiniteType approximation.toBi)
    (closedImmersion_toLimitBaseChange :
      IsClosedImmersion (pullback.lift toS approximation.toW approximation.comm.w.symm))
    (toImage : Xsys ⟶
      baseChangeOverDiagram D (OrderDual.toDual i) approximation.toBi)
    (image : ∀ j : Over (OrderDual.toDual i),
      IsSchemeTheoreticImage
        ((approximation.baseChangeCone D c).π.app j) (xCone.π.app j) (toImage.app j))
    (isLimit : IsLimit xCone) :
    (ofDiagram D c i Xsys xCone toS approximation finiteType_toBi
        closedImmersion_toLimitBaseChange toImage image isLimit).approximation =
      approximation :=
  sorry

/-- The explicit constructor retains the supplied image factorization. -/
theorem ofDiagram_toImage {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (i : I)
    (Xsys : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S) (xCone : Cone Xsys)
    (toS : xCone.pt ⟶ c.pt)
    (approximation : FiniteTypeApproximationDiagram toS (c.π.app i))
    (finiteType_toBi : FiniteType approximation.toBi)
    (closedImmersion_toLimitBaseChange :
      IsClosedImmersion (pullback.lift toS approximation.toW approximation.comm.w.symm))
    (toImage : Xsys ⟶
      baseChangeOverDiagram D (OrderDual.toDual i) approximation.toBi)
    (image : ∀ j : Over (OrderDual.toDual i),
      IsSchemeTheoreticImage
        ((approximation.baseChangeCone D c).π.app j) (xCone.π.app j) (toImage.app j))
    (isLimit : IsLimit xCone) :
    (ofDiagram D c i Xsys xCone toS approximation finiteType_toBi
        closedImmersion_toLimitBaseChange toImage image isLimit).toImage =
      toImage :=
  sorry

/-- The explicit constructor retains the supplied limit witness. -/
theorem ofDiagram_isLimit {I : Type u} [Preorder I] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (i : I)
    (Xsys : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S) (xCone : Cone Xsys)
    (toS : xCone.pt ⟶ c.pt)
    (approximation : FiniteTypeApproximationDiagram toS (c.π.app i))
    (finiteType_toBi : FiniteType approximation.toBi)
    (closedImmersion_toLimitBaseChange :
      IsClosedImmersion (pullback.lift toS approximation.toW approximation.comm.w.symm))
    (toImage : Xsys ⟶
      baseChangeOverDiagram D (OrderDual.toDual i) approximation.toBi)
    (image : ∀ j : Over (OrderDual.toDual i),
      IsSchemeTheoreticImage
        ((approximation.baseChangeCone D c).π.app j) (xCone.π.app j) (toImage.app j))
    (isLimit : IsLimit xCone) :
    (ofDiagram D c i Xsys xCone toS approximation finiteType_toBi
        closedImmersion_toLimitBaseChange toImage image isLimit).isLimit =
      isLimit :=
  sorry

/-- A finite-type approximation limit system records finite type of `W ⟶ B_i`, a
closed immersion into the limiting base change, and stagewise scheme-theoretic
images. -/
theorem spec {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} {c : Cone D} {i : I}
    {Xsys : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S} {xCone : Cone Xsys}
    {toS : xCone.pt ⟶ c.pt}
    (sys : FiniteTypeApproximationLimitSystem D c i Xsys xCone toS) :
    FiniteType sys.approximation.toBi ∧
      IsClosedImmersion
        (pullback.lift toS sys.approximation.toW sys.approximation.comm.w.symm) ∧
      ∀ j : Over (OrderDual.toDual i),
        IsSchemeTheoreticImage
          ((sys.approximation.baseChangeCone D c).π.app j)
          (xCone.π.app j) (sys.toImage.app j) :=
  sorry

/-- The structural morphism from the image system to the tail of the base diagram. -/
def toBase {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} {c : Cone D} {i : I}
    {Xsys : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S} {xCone : Cone Xsys}
    {toS : xCone.pt ⟶ c.pt}
    (sys : FiniteTypeApproximationLimitSystem D c i Xsys xCone toS) :
    Xsys ⟶ tailBaseDiagram D i :=
  sys.toImage ≫ baseChangeOverToTail D i sys.approximation.toBi

/-- A morphism between two limiting finite-type approximation systems descends to a
morphism over the base after restricting both systems to a common tail. -/
theorem exists_morphism
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    {i₁ i₂ : I}
    {Xsys : Over (OrderDual.toDual i₁) ⥤ AlgebraicSpace S}
    {Ysys : Over (OrderDual.toDual i₂) ⥤ AlgebraicSpace S}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToBase : Xsys ⟶ tailBaseDiagram D i₁) (yToBase : Ysys ⟶ tailBaseDiagram D i₂)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    (xCone_toBase : ∀ j : Over (OrderDual.toDual i₁),
      xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
    (yCone_toBase : ∀ j : Over (OrderDual.toDual i₂),
      yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
    [QuasiSeparated xToS] [FiniteType xToS]
    [QuasiSeparated yToS] [FiniteType yToS]
    (Xapprox : FiniteTypeApproximationLimitSystem D c i₁ Xsys xCone xToS)
    (Yapprox : FiniteTypeApproximationLimitSystem D c i₂ Ysys yCone yToS)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS) :
    ∃ (i₀ : I) (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀),
      ∃ φ : InverseSystemMorphismOverBase D i₀
        (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
        (restrictTailToBase D hi₁ xToBase) (restrictTailToBase D hi₂ yToBase),
        φ.IsLimitMorphism
          (Cone.whisker (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁)) xCone)
          (Cone.whisker (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂)) yCone) f :=
  sorry

end FiniteTypeApproximationLimitSystem

namespace InverseSystemMorphismOverBase

/-- Two morphisms between common tails of finite-type approximation systems that induce
the same morphism of their limit algebraic spaces agree at every sufficiently late
stage. -/
theorem eventually_eq_of_isLimitMorphism
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    {i₁ i₂ : I}
    {Xsys : Over (OrderDual.toDual i₁) ⥤ AlgebraicSpace S}
    {Ysys : Over (OrderDual.toDual i₂) ⥤ AlgebraicSpace S}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToBase : Xsys ⟶ tailBaseDiagram D i₁) (yToBase : Ysys ⟶ tailBaseDiagram D i₂)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    (xCone_toBase : ∀ j : Over (OrderDual.toDual i₁),
      xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
    (yCone_toBase : ∀ j : Over (OrderDual.toDual i₂),
      yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
    [QuasiSeparated xToS] [FiniteType xToS]
    [QuasiSeparated yToS] [FiniteType yToS]
    (Xapprox : FiniteTypeApproximationLimitSystem D c i₁ Xsys xCone xToS)
    (Yapprox : FiniteTypeApproximationLimitSystem D c i₂ Ysys yCone yToS)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS)
    {i₀ : I} (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀)
    (φ ψ : InverseSystemMorphismOverBase D i₀
      (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
      (restrictTailToBase D hi₁ xToBase) (restrictTailToBase D hi₂ yToBase))
    (hφ : φ.IsLimitMorphism
      (Cone.whisker (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁)) xCone)
      (Cone.whisker (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂)) yCone) f)
    (hψ : ψ.IsLimitMorphism
      (Cone.whisker (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁)) xCone)
      (Cone.whisker (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂)) yCone) f) :
    ∃ (i : I) (hi₀i : i₀ ≤ i), ∀ ⦃j : I⦄ (hij : i ≤ j),
      φ.hom.app (tailObject j (le_trans hi₀i hij)) =
        ψ.hom.app (tailObject j (le_trans hi₀i hij)) :=
  sorry

end InverseSystemMorphismOverBase


end AlgebraicGeometry.AlgebraicSpace
