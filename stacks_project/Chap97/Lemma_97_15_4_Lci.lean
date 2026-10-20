module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Lci

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

#check (AlgebraicGeometry.FiniteHilbertStack.Obj.IsLci :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y) {d : ℕ},
    Obj F d → Prop)

#check (AlgebraicGeometry.FiniteHilbertStack.lciP_isStack :
  ∀ {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] (d : ℕ),
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (lciP F d))

#check (AlgebraicGeometry.FiniteHilbertStack.lciStack :
  ∀ {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] (d : ℕ),
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S))

#check (AlgebraicGeometry.FiniteHilbertStack.lciForgetToY :
  ∀ {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] (d : ℕ), lciStack F d ⟶ 𝒴)
