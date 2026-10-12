/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper

/-!
# Finite-presentation approximation of proper morphisms

This file records directed limit presentations of proper scheme morphisms by proper,
finite-presentation stages with closed-immersion transition maps and projections.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation

/-- Fixed data form a proper closed-immersion finite-presentation approximation when their cone
is limiting, their structure maps are compatible over the base and recover the original
morphism, every stage map is proper and of finite presentation, and every transition map and
limit projection is a closed immersion. -/
def IsProperClosedImmersion {I : Type u} [Preorder I]
    {X S : Scheme.{u}} (f : X ⟶ S) (D : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : ∀ j : I, D.obj j ⟶ S) : Prop :=
  Nonempty (IsLimit (⟨X, π⟩ : Cone D)) ∧
    (∀ {j k : I} (hjk : j ≤ k), D.map (homOfLE hjk) ≫ σ j = σ k) ∧
    (∀ j : I, π.app j ≫ σ j = f) ∧
    (∀ j : I, IsProper (σ j)) ∧
    (∀ j : I, Scheme.Hom.FinitePresentation (σ j)) ∧
    (∀ {j k : I} (hjk : j ≤ k), IsClosedImmersion (D.map (homOfLE hjk))) ∧
    ∀ j : I, IsClosedImmersion (π.app j)

/-- A proper closed-immersion finite-presentation approximation is equivalently a limiting
compatible system over the base that recovers the original morphism, has proper,
finite-presentation stage maps, and has closed-immersion transitions and limit projections. -/
theorem isProperClosedImmersion_iff
    {I : Type u} [Preorder I] {X S : Scheme.{u}} (f : X ⟶ S)
    (D : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : ∀ j : I, D.obj j ⟶ S) :
    IsProperClosedImmersion f D π σ ↔
      Nonempty (IsLimit (⟨X, π⟩ : Cone D)) ∧
        (∀ {j k : I} (hjk : j ≤ k), D.map (homOfLE hjk) ≫ σ j = σ k) ∧
        (∀ j : I, π.app j ≫ σ j = f) ∧
        (∀ j : I, IsProper (σ j)) ∧
        (∀ j : I, Scheme.Hom.FinitePresentation (σ j)) ∧
        (∀ {j k : I} (hjk : j ≤ k), IsClosedImmersion (D.map (homOfLE hjk))) ∧
        ∀ j : I, IsClosedImmersion (π.app j) := sorry

/-- A proper morphism to a quasi-compact, quasi-separated scheme admits a directed limiting
presentation by proper finite-presentation stages whose transition maps and limit projections
are closed immersions. -/
theorem exists_of_isProper {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
      ∃ (_ : IsDirected I (· ≤ ·)), ∃ (D : OrderDual I ⥤ Scheme.{u}),
        ∃ (π : (Functor.const (OrderDual I)).obj X ⟶ D),
          ∃ (σ : ∀ j : I, D.obj j ⟶ S),
            IsProperClosedImmersion f D π σ := sorry

end AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation

namespace AlgebraicGeometry.FinitePresentationApproximationLimitSystem

/-- A morphism between finite-presentation approximation systems that induces a proper
morphism on their limits is proper at every sufficiently late stage. -/
theorem exists_eventually_isProper
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j : I, IsNoetherian (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    {i₁ i₂ : I}
    {Xsys : Over (OrderDual.toDual i₁) ⥤ Scheme.{u}}
    {Ysys : Over (OrderDual.toDual i₂) ⥤ Scheme.{u}}
    (xCone : Cone Xsys) (yCone : Cone Ysys)
    (xToBase : Xsys ⟶ tailBaseDiagram D i₁)
    (yToBase : Ysys ⟶ tailBaseDiagram D i₂)
    (xToS : xCone.pt ⟶ c.pt) (yToS : yCone.pt ⟶ c.pt)
    (xCone_toBase : ∀ j : Over (OrderDual.toDual i₁),
      xCone.π.app j ≫ xToBase.app j = xToS ≫ c.π.app j.left)
    (yCone_toBase : ∀ j : Over (OrderDual.toDual i₂),
      yCone.π.app j ≫ yToBase.app j = yToS ≫ c.π.app j.left)
    [QuasiSeparated xToS] [Scheme.Hom.FiniteType xToS]
    [QuasiSeparated yToS] [Scheme.Hom.FiniteType yToS]
    (Xapprox : FinitePresentationApproximationLimitSystem D c i₁ Xsys xCone xToS)
    (Yapprox : FinitePresentationApproximationLimitSystem D c i₂ Ysys yCone yToS)
    (f : xCone.pt ⟶ yCone.pt) (hf_overS : f ≫ yToS = xToS) [IsProper f]
    (i₀ : I) (hi₁ : i₁ ≤ i₀) (hi₂ : i₂ ≤ i₀)
    (φ : InverseSystemMorphismOverBase D i₀
      (restrictTail hi₁ Xsys) (restrictTail hi₂ Ysys)
      (restrictTailToBase D hi₁ xToBase) (restrictTailToBase D hi₂ yToBase))
    (hφ : φ.IsLimitMorphism (Cone.whisker
      (Over.map (homOfLE hi₁ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₁)) xCone)
      (Cone.whisker
        (Over.map (homOfLE hi₂ : OrderDual.toDual i₀ ⟶ OrderDual.toDual i₂)) yCone) f) :
    ∃ (i₃ : I) (hi₀i₃ : i₀ ≤ i₃), ∀ ⦃i : I⦄ (hi₃i : i₃ ≤ i),
      IsProper (φ.hom.app (tailObject i (le_trans hi₀i₃ hi₃i))) := sorry

end AlgebraicGeometry.FinitePresentationApproximationLimitSystem
