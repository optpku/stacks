module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Limit.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Diagram
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage

/-!
# Finite-type approximation systems over directed limits

This leaf packages inverse systems over a tail of a directed base diagram, their morphisms over
the base, and the finite-presentation approximation data used to descend a morphism between the
limit schemes.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The base inverse system restricted to stages `j >= i0`. -/
abbrev tailBaseDiagram {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (i0 : I) :
    Over (show OrderDual I from i0) ⥤ Scheme.{u} :=
  Over.forget (show OrderDual I from i0) ⋙ D

/-- The object of the tail category represented by a stage `j >= i0`. -/
abbrev tailObject {I : Type u} [Preorder I] {i0 : I} (j : I) (h : i0 ≤ j) :
    Over (show OrderDual I from i0) :=
  Over.mk (homOfLE h : (show OrderDual I from j) ⟶ (show OrderDual I from i0))

/-- Restrict an inverse system starting at `i` to a later tail starting at `i0`. -/
abbrev restrictTail {I : Type u} [Preorder I]
    {i i0 : I} (h : i ≤ i0)
    (Xsys : Over (show OrderDual I from i) ⥤ Scheme.{u}) :
    Over (show OrderDual I from i0) ⥤ Scheme.{u} :=
  Over.map (homOfLE h : (show OrderDual I from i0) ⟶ (show OrderDual I from i)) ⋙ Xsys

/-- Restrict the structural map from an inverse system to the base system to a later tail. -/
abbrev restrictTailToBase {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) {i i0 : I} (h : i ≤ i0)
    {Xsys : Over (show OrderDual I from i) ⥤ Scheme.{u}}
    (xToBase : Xsys ⟶ tailBaseDiagram D i) :
    restrictTail h Xsys ⟶ tailBaseDiagram D i0 :=
  Functor.whiskerLeft
    (Over.map (homOfLE h : (show OrderDual I from i0) ⟶ (show OrderDual I from i)))
    xToBase

/-- A morphism of inverse systems over the same tail of the base system. -/
abbrev InverseSystemMorphismOverBase {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (i0 : I)
    (Xsys Ysys : Over (show OrderDual I from i0) ⥤ Scheme.{u})
    (xToBase : Xsys ⟶ tailBaseDiagram D i0)
    (yToBase : Ysys ⟶ tailBaseDiagram D i0) :=
  (Over.mk xToBase : Over (tailBaseDiagram D i0)) ⟶ Over.mk yToBase

namespace InverseSystemMorphismOverBase

/-- The underlying natural transformation of a morphism of inverse systems over a base. -/
abbrev hom {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Scheme.{u}} {i0 : I}
    {Xsys Ysys : Over (show OrderDual I from i0) ⥤ Scheme.{u}}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0}
    {yToBase : Ysys ⟶ tailBaseDiagram D i0}
    (φ : InverseSystemMorphismOverBase D i0 Xsys Ysys xToBase yToBase) :
    Xsys ⟶ Ysys :=
  φ.left

/-- The underlying natural transformation of a morphism over a base commutes with the
structural maps. -/
theorem over_base {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Scheme.{u}} {i0 : I}
    {Xsys Ysys : Over (show OrderDual I from i0) ⥤ Scheme.{u}}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0}
    {yToBase : Ysys ⟶ tailBaseDiagram D i0}
    (φ : InverseSystemMorphismOverBase D i0 Xsys Ysys xToBase yToBase) :
    φ.hom ≫ yToBase = xToBase :=
  φ.w

/-- The identity morphism of an inverse system over a base. -/
def id {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Scheme.{u}} {i0 : I}
    {Xsys : Over (show OrderDual I from i0) ⥤ Scheme.{u}}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0} :
    InverseSystemMorphismOverBase D i0 Xsys Xsys xToBase xToBase :=
  𝟙 (Over.mk xToBase)

/-- Composition of morphisms of inverse systems over a common base. -/
def comp {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Scheme.{u}} {i0 : I}
    {Xsys Ysys Zsys : Over (show OrderDual I from i0) ⥤ Scheme.{u}}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0}
    {yToBase : Ysys ⟶ tailBaseDiagram D i0}
    {zToBase : Zsys ⟶ tailBaseDiagram D i0}
    (φ : InverseSystemMorphismOverBase D i0 Xsys Ysys xToBase yToBase)
    (ψ : InverseSystemMorphismOverBase D i0 Ysys Zsys yToBase zToBase) :
    InverseSystemMorphismOverBase D i0 Xsys Zsys xToBase zToBase :=
  φ ≫ ψ

/-- A morphism of inverse systems induces the specified morphism on the limit cones. -/
def IsLimitMorphism {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Scheme.{u}} {i0 : I}
    {Xsys Ysys : Over (show OrderDual I from i0) ⥤ Scheme.{u}}
    {xToBase : Xsys ⟶ tailBaseDiagram D i0}
    {yToBase : Ysys ⟶ tailBaseDiagram D i0}
    (φ : InverseSystemMorphismOverBase D i0 Xsys Ysys xToBase yToBase)
    (xCone : Cone Xsys) (yCone : Cone Ysys) (f : xCone.pt ⟶ yCone.pt) : Prop :=
  ∀ j : Over (show OrderDual I from i0),
    f ≫ yCone.π.app j = xCone.π.app j ≫ φ.hom.app j

end InverseSystemMorphismOverBase

/-- A finite-presentation approximation system whose cone is the limit, with each stage the
scheme-theoretic image in the associated base-change system. -/
structure FinitePresentationApproximationLimitSystem {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    (Xsys : Over (show OrderDual I from i) ⥤ Scheme.{u}) (xCone : Cone Xsys)
    (toS : xCone.pt ⟶ c.pt) where
  /-- The finite-type approximation diagram at the initial stage. -/
  approximation : FiniteTypeApproximationDiagram toS (c.π.app i)
  /-- The structural morphism of the approximation diagram is of finite presentation. -/
  finitePresentation_toSi : Scheme.Hom.FinitePresentation approximation.toSi
  /-- The induced morphism to the limiting base change is a closed immersion. -/
  closedImmersion_toLimitBaseChange :
    IsClosedImmersion (pullback.lift toS approximation.toW approximation.w.symm)
  /-- The stage system maps into the stagewise base-change system. -/
  toImage : Xsys ⟶
    Scheme.baseChangeOverDiagram D (show OrderDual I from i) approximation.toSi
  /-- Each stage is the scheme-theoretic image of `X` in the corresponding base change. -/
  image : ∀ j : Over (show OrderDual I from i),
    IsSchemeTheoreticImageFactorization
      ((approximation.baseChangeCone D c).π.app j) (xCone.π.app j) (toImage.app j)
  /-- The cone with vertex `X` is the limit cone for the approximation system. -/
  isLimit : IsLimit xCone

namespace FinitePresentationApproximationLimitSystem

/-- Construct a limiting finite-presentation approximation system from its approximation diagram,
closed-immersion and scheme-theoretic-image data, and limiting cone. -/
def ofDiagram {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    (Xsys : Over (show OrderDual I from i) ⥤ Scheme.{u}) (xCone : Cone Xsys)
    (toS : xCone.pt ⟶ c.pt)
    (approximation : FiniteTypeApproximationDiagram toS (c.π.app i))
    (finitePresentation_toSi : Scheme.Hom.FinitePresentation approximation.toSi)
    (closedImmersion_toLimitBaseChange :
      IsClosedImmersion (pullback.lift toS approximation.toW approximation.w.symm))
    (toImage : Xsys ⟶
      Scheme.baseChangeOverDiagram D (show OrderDual I from i) approximation.toSi)
    (image : ∀ j : Over (show OrderDual I from i),
      IsSchemeTheoreticImageFactorization
        ((approximation.baseChangeCone D c).π.app j) (xCone.π.app j) (toImage.app j))
    (isLimit : IsLimit xCone) :
    FinitePresentationApproximationLimitSystem D c i Xsys xCone toS where
  approximation := approximation
  finitePresentation_toSi := finitePresentation_toSi
  closedImmersion_toLimitBaseChange := closedImmersion_toLimitBaseChange
  toImage := toImage
  image := image
  isLimit := isLimit

/-- The explicit constructor for a limiting finite-presentation approximation system retains its
diagram, finite-presentation and closed-immersion facts, image factorization, and limit witness. -/
theorem ofDiagram_spec {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (i : I)
    (Xsys : Over (show OrderDual I from i) ⥤ Scheme.{u}) (xCone : Cone Xsys)
    (toS : xCone.pt ⟶ c.pt)
    (approximation : FiniteTypeApproximationDiagram toS (c.π.app i))
    (finitePresentation_toSi : Scheme.Hom.FinitePresentation approximation.toSi)
    (closedImmersion_toLimitBaseChange :
      IsClosedImmersion (pullback.lift toS approximation.toW approximation.w.symm))
    (toImage : Xsys ⟶
      Scheme.baseChangeOverDiagram D (show OrderDual I from i) approximation.toSi)
    (image : ∀ j : Over (show OrderDual I from i),
      IsSchemeTheoreticImageFactorization
        ((approximation.baseChangeCone D c).π.app j) (xCone.π.app j) (toImage.app j))
    (isLimit : IsLimit xCone) :
    (ofDiagram D c i Xsys xCone toS approximation finitePresentation_toSi
        closedImmersion_toLimitBaseChange toImage image isLimit).approximation = approximation ∧
      (ofDiagram D c i Xsys xCone toS approximation finitePresentation_toSi
        closedImmersion_toLimitBaseChange toImage image isLimit).finitePresentation_toSi =
          finitePresentation_toSi ∧
      (ofDiagram D c i Xsys xCone toS approximation finitePresentation_toSi
        closedImmersion_toLimitBaseChange toImage image isLimit).closedImmersion_toLimitBaseChange =
          closedImmersion_toLimitBaseChange ∧
      (ofDiagram D c i Xsys xCone toS approximation finitePresentation_toSi
        closedImmersion_toLimitBaseChange toImage image isLimit).toImage = toImage ∧
      (ofDiagram D c i Xsys xCone toS approximation finitePresentation_toSi
        closedImmersion_toLimitBaseChange toImage image isLimit).image = image ∧
      (ofDiagram D c i Xsys xCone toS approximation finitePresentation_toSi
        closedImmersion_toLimitBaseChange toImage image isLimit).isLimit = isLimit := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A morphism between two limiting finite-presentation approximation systems descends to a
morphism over the base after restricting both systems to a common tail. -/
theorem exists_morphism
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    {i₁ i₂ : I}
    {Xsys : Over (show OrderDual I from i₁) ⥤ Scheme.{u}}
    {Ysys : Over (show OrderDual I from i₂) ⥤ Scheme.{u}}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToBase : Xsys ⟶ tailBaseDiagram D i₁)
    (yToBase : Ysys ⟶ tailBaseDiagram D i₂)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    (xCone_toBase : ∀ j : Over (show OrderDual I from i₁),
      xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
    (yCone_toBase : ∀ j : Over (show OrderDual I from i₂),
      yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
    [QuasiSeparated xToS] [Scheme.Hom.FiniteType xToS]
    [QuasiSeparated yToS] [Scheme.Hom.FiniteType yToS]
    (Xapprox : FinitePresentationApproximationLimitSystem D c i₁ Xsys xCone xToS)
    (Yapprox : FinitePresentationApproximationLimitSystem D c i₂ Ysys yCone yToS)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS) :
    ∃ (i₀ : I) (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀),
      ∃ φ : InverseSystemMorphismOverBase D i₀
        (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
        (restrictTailToBase D hi₁ xToBase) (restrictTailToBase D hi₂ yToBase),
        φ.IsLimitMorphism (Cone.whisker
          (Over.map (homOfLE hi₁ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₁)))
          xCone)
          (Cone.whisker
            (Over.map (homOfLE hi₂ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₂)))
            yCone) f := sorry

end FinitePresentationApproximationLimitSystem

namespace InverseSystemMorphismOverBase

/-- Two morphisms between common tails of finite-presentation approximation systems that induce
the same morphism of their limit schemes agree at every sufficiently late stage. -/
theorem eventually_eq_of_isLimitMorphism
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    {i₁ i₂ : I}
    {Xsys : Over (show OrderDual I from i₁) ⥤ Scheme.{u}}
    {Ysys : Over (show OrderDual I from i₂) ⥤ Scheme.{u}}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToBase : Xsys ⟶ tailBaseDiagram D i₁)
    (yToBase : Ysys ⟶ tailBaseDiagram D i₂)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    (xCone_toBase : ∀ j : Over (show OrderDual I from i₁),
      xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
    (yCone_toBase : ∀ j : Over (show OrderDual I from i₂),
      yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
    [QuasiSeparated xToS] [Scheme.Hom.FiniteType xToS]
    [QuasiSeparated yToS] [Scheme.Hom.FiniteType yToS]
    (Xapprox : FinitePresentationApproximationLimitSystem D c i₁ Xsys xCone xToS)
    (Yapprox : FinitePresentationApproximationLimitSystem D c i₂ Ysys yCone yToS)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS)
    {i₀ : I} (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀)
    (φ ψ : InverseSystemMorphismOverBase D i₀
      (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
      (restrictTailToBase D hi₁ xToBase) (restrictTailToBase D hi₂ yToBase))
    (hφ : φ.IsLimitMorphism (Cone.whisker
      (Over.map (homOfLE hi₁ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₁)))
      xCone)
      (Cone.whisker
        (Over.map (homOfLE hi₂ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₂)))
        yCone) f)
    (hψ : ψ.IsLimitMorphism (Cone.whisker
      (Over.map (homOfLE hi₁ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₁)))
      xCone)
      (Cone.whisker
        (Over.map (homOfLE hi₂ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₂)))
        yCone) f) :
    ∃ (i : I) (hi₀i : i₀ ≤ i), ∀ ⦃j : I⦄ (hij : i ≤ j),
      φ.hom.app (tailObject j (le_trans hi₀i hij)) =
        ψ.hom.app (tailObject j (le_trans hi₀i hij)) := sorry

end InverseSystemMorphismOverBase

namespace FinitePresentationApproximationLimitSystem

/-- A morphism between quasi-separated finite-type schemes over a directed affine limit descends
to their finite-presentation approximation systems on a common tail, and any two descended
morphisms inducing the given limit morphism eventually agree. -/
@[stacks 0CNR]
theorem exists_morphism_eventually_unique
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    {i₁ i₂ : I}
    {Xsys : Over (show OrderDual I from i₁) ⥤ Scheme.{u}}
    {Ysys : Over (show OrderDual I from i₂) ⥤ Scheme.{u}}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToBase : Xsys ⟶ tailBaseDiagram D i₁)
    (yToBase : Ysys ⟶ tailBaseDiagram D i₂)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    (xCone_toBase : ∀ j : Over (show OrderDual I from i₁),
      xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
    (yCone_toBase : ∀ j : Over (show OrderDual I from i₂),
      yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
    [QuasiSeparated xToS] [Scheme.Hom.FiniteType xToS]
    [QuasiSeparated yToS] [Scheme.Hom.FiniteType yToS]
    (Xapprox : FinitePresentationApproximationLimitSystem D c i₁ Xsys xCone xToS)
    (Yapprox : FinitePresentationApproximationLimitSystem D c i₂ Ysys yCone yToS)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS) :
    ∃ (i₀ : I) (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀),
      ∃ φ : InverseSystemMorphismOverBase D i₀
        (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
        (restrictTailToBase D hi₁ xToBase) (restrictTailToBase D hi₂ yToBase),
        φ.IsLimitMorphism (Cone.whisker
          (Over.map (homOfLE hi₁ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₁)))
          xCone)
          (Cone.whisker
            (Over.map (homOfLE hi₂ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₂)))
            yCone) f ∧
        ∀ ψ : InverseSystemMorphismOverBase D i₀
            (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
            (restrictTailToBase D hi₁ xToBase) (restrictTailToBase D hi₂ yToBase),
          ψ.IsLimitMorphism (Cone.whisker
            (Over.map (homOfLE hi₁ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₁)))
            xCone)
            (Cone.whisker
              (Over.map (homOfLE hi₂ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₂)))
              yCone) f →
            ∃ (i : I) (hi₀i : i₀ ≤ i), ∀ ⦃j : I⦄ (hij : i ≤ j),
              φ.hom.app (tailObject j (le_trans hi₀i hij)) =
                ψ.hom.app (tailObject j (le_trans hi₀i hij)) := by
  obtain ⟨i₀, hi₁, hi₂, φ, hφ⟩ :=
    FinitePresentationApproximationLimitSystem.exists_morphism D c hc xCone yCone
      xToBase yToBase xToS yToS xCone_toBase yCone_toBase Xapprox Yapprox f hf_overS
  refine ⟨i₀, hi₁, hi₂, φ, hφ, ?_⟩
  intro ψ hψ
  exact InverseSystemMorphismOverBase.eventually_eq_of_isLimitMorphism D c hc xCone yCone
    xToBase yToBase xToS yToS xCone_toBase yCone_toBase Xapprox Yapprox f hf_overS
    hi₁ hi₂ φ ψ hφ hψ

/-- Two finite-presentation approximation systems of the same quasi-separated finite-type
scheme over a directed affine limit admit comparison morphisms on a common tail that induce the
identity on the limit and are mutually inverse at every sufficiently late stage. -/
@[stacks 0CNS]
theorem exists_morphisms_eventually_inverse
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (X : Scheme.{u}) {i₁ i₂ : I}
    {Xsys : Over (show OrderDual I from i₁) ⥤ Scheme.{u}}
    {Ysys : Over (show OrderDual I from i₂) ⥤ Scheme.{u}}
    (xπ : (Functor.const (Over (show OrderDual I from i₁))).obj X ⟶ Xsys)
    (yπ : (Functor.const (Over (show OrderDual I from i₂))).obj X ⟶ Ysys)
    (xToBase : Xsys ⟶ tailBaseDiagram D i₁)
    (yToBase : Ysys ⟶ tailBaseDiagram D i₂)
    (toS : X ⟶ c.pt)
    (xCone_toBase : ∀ j : Over (show OrderDual I from i₁),
      xπ.app j ≫ xToBase.app j = toS ≫ c.π.app j.left)
    (yCone_toBase : ∀ j : Over (show OrderDual I from i₂),
      yπ.app j ≫ yToBase.app j = toS ≫ c.π.app j.left)
    [QuasiSeparated toS] [Scheme.Hom.FiniteType toS]
    (Xapprox : FinitePresentationApproximationLimitSystem D c i₁ Xsys
      (⟨X, xπ⟩ : Cone Xsys) toS)
    (Yapprox : FinitePresentationApproximationLimitSystem D c i₂ Ysys
      (⟨X, yπ⟩ : Cone Ysys) toS) :
    ∃ (i₀ : I) (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀),
      ∃ φ : InverseSystemMorphismOverBase D i₀
          (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
          (restrictTailToBase D hi₁ xToBase) (restrictTailToBase D hi₂ yToBase),
        φ.IsLimitMorphism (Cone.whisker
          (Over.map (homOfLE hi₁ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₁)))
          (⟨X, xπ⟩ : Cone Xsys))
          (Cone.whisker
            (Over.map (homOfLE hi₂ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₂)))
            (⟨X, yπ⟩ : Cone Ysys)) (𝟙 X) ∧
        ∃ ψ : InverseSystemMorphismOverBase D i₀
            (restrictTail hi₂ Ysys) (restrictTail hi₁ Xsys)
            (restrictTailToBase D hi₂ yToBase) (restrictTailToBase D hi₁ xToBase),
          ψ.IsLimitMorphism (Cone.whisker
            (Over.map (homOfLE hi₂ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₂)))
            (⟨X, yπ⟩ : Cone Ysys))
            (Cone.whisker
              (Over.map (homOfLE hi₁ : (show OrderDual I from i₀) ⟶ (show OrderDual I from i₁)))
              (⟨X, xπ⟩ : Cone Xsys)) (𝟙 X) ∧
          ∃ (i : I) (hi₀i : i₀ ≤ i), ∀ {j : I} (hij : i ≤ j),
            (InverseSystemMorphismOverBase.comp φ ψ).hom.app
                (tailObject j (le_trans hi₀i hij)) =
              (InverseSystemMorphismOverBase.id (D := D) (i0 := i₀)
                (Xsys := restrictTail hi₁ Xsys)
                (xToBase := restrictTailToBase D hi₁ xToBase)).hom.app
                  (tailObject j (le_trans hi₀i hij)) ∧
            (InverseSystemMorphismOverBase.comp ψ φ).hom.app
                (tailObject j (le_trans hi₀i hij)) =
              (InverseSystemMorphismOverBase.id (D := D) (i0 := i₀)
                (Xsys := restrictTail hi₂ Ysys)
                (xToBase := restrictTailToBase D hi₂ yToBase)).hom.app
                  (tailObject j (le_trans hi₀i hij)) := sorry

end FinitePresentationApproximationLimitSystem

end AlgebraicGeometry
