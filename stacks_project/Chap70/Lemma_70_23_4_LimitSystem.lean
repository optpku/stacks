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

#check (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationLimitSystem :
  ∀ {I : Type u} [Preorder I]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (i : I)
    (Xsys : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S) (xCone : Cone Xsys)
    (toS : xCone.pt ⟶ c.pt),
    Type (u + 1))

namespace FiniteTypeApproximationLimitSystem

#check (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationLimitSystem.ofDiagram :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
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
    (isLimit : IsLimit xCone),
    FiniteTypeApproximationLimitSystem D c i Xsys xCone toS)

#check (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationLimitSystem.ofDiagram_approximation :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
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
    (isLimit : IsLimit xCone),
    (ofDiagram D c i Xsys xCone toS approximation finiteType_toBi
        closedImmersion_toLimitBaseChange toImage image isLimit).approximation =
      approximation)

#check (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationLimitSystem.ofDiagram_toImage :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
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
    (isLimit : IsLimit xCone),
    (ofDiagram D c i Xsys xCone toS approximation finiteType_toBi
        closedImmersion_toLimitBaseChange toImage image isLimit).toImage =
      toImage)

#check (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationLimitSystem.ofDiagram_isLimit :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
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
    (isLimit : IsLimit xCone),
    (ofDiagram D c i Xsys xCone toS approximation finiteType_toBi
        closedImmersion_toLimitBaseChange toImage image isLimit).isLimit =
      isLimit)

#check (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationLimitSystem.spec :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} {c : Cone D} {i : I}
    {Xsys : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S} {xCone : Cone Xsys}
    {toS : xCone.pt ⟶ c.pt}
    (sys : FiniteTypeApproximationLimitSystem D c i Xsys xCone toS),
    FiniteType sys.approximation.toBi ∧
      IsClosedImmersion
        (pullback.lift toS sys.approximation.toW sys.approximation.comm.w.symm) ∧
      ∀ j : Over (OrderDual.toDual i),
        IsSchemeTheoreticImage
          ((sys.approximation.baseChangeCone D c).π.app j)
          (xCone.π.app j) (sys.toImage.app j))

#check (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationLimitSystem.toBase :
  ∀ {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} {c : Cone D} {i : I}
    {Xsys : Over (OrderDual.toDual i) ⥤ AlgebraicSpace S} {xCone : Cone Xsys}
    {toS : xCone.pt ⟶ c.pt}
    (sys : FiniteTypeApproximationLimitSystem D c i Xsys xCone toS),
    Xsys ⟶ tailBaseDiagram D i)

#check (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationLimitSystem.exists_morphism :
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    {i₁ i₂ : I}
    {Xsys : Over (OrderDual.toDual i₁) ⥤ AlgebraicSpace S}
    {Ysys : Over (OrderDual.toDual i₂) ⥤ AlgebraicSpace S}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    [QuasiSeparated xToS] [FiniteType xToS]
    [QuasiSeparated yToS] [FiniteType yToS]
    (Xapprox : FiniteTypeApproximationLimitSystem D c i₁ Xsys xCone xToS)
    (Yapprox : FiniteTypeApproximationLimitSystem D c i₂ Ysys yCone yToS)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS),
    ∃ (i₀ : I) (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀),
      ∃ φ : InverseSystemMorphismOverBase D i₀
        (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
        (restrictTailToBase D hi₁ Xapprox.toBase) (restrictTailToBase D hi₂ Yapprox.toBase),
        φ.IsLimitMorphism
          (Cone.whisker (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁)) xCone)
          (Cone.whisker (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂)) yCone) f)

end FiniteTypeApproximationLimitSystem

namespace InverseSystemMorphismOverBase

#check (AlgebraicGeometry.AlgebraicSpace.InverseSystemMorphismOverBase.eventually_eq_of_isLimitMorphism :
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    {i₁ i₂ : I}
    {Xsys : Over (OrderDual.toDual i₁) ⥤ AlgebraicSpace S}
    {Ysys : Over (OrderDual.toDual i₂) ⥤ AlgebraicSpace S}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    [QuasiSeparated xToS] [FiniteType xToS]
    [QuasiSeparated yToS] [FiniteType yToS]
    (Xapprox : FiniteTypeApproximationLimitSystem D c i₁ Xsys xCone xToS)
    (Yapprox : FiniteTypeApproximationLimitSystem D c i₂ Ysys yCone yToS)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS)
    {i₀ : I} (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀)
    (φ ψ : InverseSystemMorphismOverBase D i₀
      (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
      (restrictTailToBase D hi₁ Xapprox.toBase) (restrictTailToBase D hi₂ Yapprox.toBase))
    (hφ : φ.IsLimitMorphism
      (Cone.whisker (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁)) xCone)
      (Cone.whisker (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂)) yCone) f)
    (hψ : ψ.IsLimitMorphism
      (Cone.whisker (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁)) xCone)
      (Cone.whisker (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂)) yCone) f),
    ∃ (i : I) (hi₀i : i₀ ≤ i), ∀ ⦃j : I⦄ (hij : i ≤ j),
      φ.hom.app (tailObject j (le_trans hi₀i hij)) =
        ψ.hom.app (tailObject j (le_trans hi₀i hij)))

end InverseSystemMorphismOverBase

end AlgebraicGeometry.AlgebraicSpace
