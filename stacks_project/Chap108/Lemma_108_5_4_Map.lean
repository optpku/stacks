module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Pushforward
public import stacks_project.Chap99.«99_8_1_1_Functor»

/-!
# Fibre comparison and pushforward on the proper-support Quot functor
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- The morphism of fibres induced by a morphism over the base. -/
#check (AlgebraicGeometry.AlgebraicSpace.Quot.fiberComparison :
  ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (π : X ⟶ Y) (y : Y ⟶ B)
    (σ : SchemeOver B), Quot.fiber (π ≫ y) σ ⟶ Quot.fiber y σ)

/- Fibrewise pushforward of proper-support quotient representatives. -/
#check (AlgebraicGeometry.AlgebraicSpace.Quot.QuotPoint.pushforward :
  ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (π : X ⟶ Y) (y : Y ⟶ B)
    {F : X.Modules} {σ : SchemeOver B} [Affine π] [QuasiFinite π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)] [Separated y]
    [FinitePresentation y] [F.IsQuasicoherent],
    Quot.QuotPoint (π ≫ y) F σ → Quot.QuotPoint y ((Modules.pushforward π).obj F) σ)
