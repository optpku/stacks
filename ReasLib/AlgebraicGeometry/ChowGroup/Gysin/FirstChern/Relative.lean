module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Commutativity
import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.FirstChern
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback

/-!
# Gysin homomorphisms and first Chern classes on relative Chow groups

This file records compatibility between zero-scheme Gysin pullback and intersection
by the first Chern class of an invertible module.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Gysin pullback to the zero scheme of a section commutes with intersection by the
first Chern class after pulling back the invertible module. -/
theorem gysin_firstChernClassCap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    (𝒩 : X.left.Modules) [Scheme.Modules.Invertible 𝒩] (k : ℤ)
    (α : RelativeChow δ X k) :
    gysin δ X ℒ s (k - 1) (firstChernClassCap δ X 𝒩 k α) =
      firstChernClassCap δ (Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom))
        ((Scheme.Modules.pullback
          (Over.homMk (Scheme.zeroSchemeι ℒ s) :
            Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom) ⟶ X).left).obj 𝒩) (k - 1)
        (gysin δ X ℒ s k α) := sorry

end AlgebraicGeometry.ChowGroup
