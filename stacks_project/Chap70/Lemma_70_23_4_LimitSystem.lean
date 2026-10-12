/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_23_3_SchemeTheoreticImage
public import stacks_project.Chap70.Lemma_70_23_4_Morphism

/-!
# Finite-type approximation limit systems of algebraic spaces

This leaf packages a good finite-type approximation diagram together with a
compatible inverse system of scheme-theoretic images whose cone is a limit, and
records descent of a morphism over the base to a morphism of such systems.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

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
