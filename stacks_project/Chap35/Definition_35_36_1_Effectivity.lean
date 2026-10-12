/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Descent.MorphismProperty

/-!
# Effective descent for properties of scheme morphisms

This compatibility module reexports the reusable definitions of effectivity
and descent for properties of scheme morphisms.
-/

open CategoryTheory

universe u v

#check (AlgebraicGeometry.DescentTopology : Type)

#check (@AlgebraicGeometry.DescentTopology.precoverage :
  AlgebraicGeometry.DescentTopology → Precoverage AlgebraicGeometry.Scheme.{u})

#check (AlgebraicGeometry.DescentTopology.ofStandard :
  AlgebraicGeometry.StandardTopology → AlgebraicGeometry.DescentTopology)

#check (@AlgebraicGeometry.DescentTopology.precoverageOfStandard :
  ∀ τ : AlgebraicGeometry.StandardTopology,
    (AlgebraicGeometry.DescentTopology.ofStandard τ).precoverage = τ.precoverage)

#check (@AlgebraicGeometry.Scheme.DescentData.IsEffective :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
    {X : I → AlgebraicGeometry.Scheme.{u}} {f : ∀ i, X i ⟶ S},
      AlgebraicGeometry.Scheme.DescentData X f → Prop)

#check (@AlgebraicGeometry.Scheme.DescentData.isEffective_iff :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
    {X : I → AlgebraicGeometry.Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (D : AlgebraicGeometry.Scheme.DescentData X f),
      D.IsEffective ↔
        ∃ U : Over S, Nonempty (AlgebraicGeometry.Scheme.DescentData.ofObj X f U ≅ D))

#check (@CategoryTheory.MorphismProperty.SatisfiesDescent :
  CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u} →
    AlgebraicGeometry.DescentTopology → Prop)

#check (@CategoryTheory.MorphismProperty.satisfiesDescent_iff :
  ∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
    (τ : AlgebraicGeometry.DescentTopology),
    P.SatisfiesDescent τ ↔
      ∀ (S : AlgebraicGeometry.Scheme.{u})
        (𝒰 : AlgebraicGeometry.Scheme.Cover.{u} τ.precoverage S)
        (D : AlgebraicGeometry.Scheme.DescentData 𝒰.X 𝒰.f),
          (∀ i, P (D.obj i).hom) → D.IsEffective)

#check (@CategoryTheory.MorphismProperty.SatisfiesDescent.effective :
  ∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}}
    {τ : AlgebraicGeometry.DescentTopology}, P.SatisfiesDescent τ →
      ∀ {S : AlgebraicGeometry.Scheme.{u}}
        (𝒰 : AlgebraicGeometry.Scheme.Cover.{u} τ.precoverage S)
        (D : AlgebraicGeometry.Scheme.DescentData 𝒰.X 𝒰.f),
          (∀ i, P (D.obj i).hom) → D.IsEffective)

#check (@CategoryTheory.MorphismProperty.SatisfiesDescent.of_le :
  ∀ {P Q : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}}
    {τ : AlgebraicGeometry.DescentTopology},
    P ≤ Q → Q.SatisfiesDescent τ → P.SatisfiesDescent τ)
