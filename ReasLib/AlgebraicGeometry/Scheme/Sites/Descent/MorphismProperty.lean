module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard

/-!
# Descent for properties of scheme morphisms

This module indexes the six standard scheme topologies used in descent and
defines when a property of scheme morphisms has effective descent.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The six scheme topologies used for descent of properties of morphisms. -/
def DescentTopology := Option StandardTopology

end AlgebraicGeometry

namespace AlgebraicGeometry.DescentTopology

/-- The Zariski topology, viewed as a topology for descent. -/
@[match_pattern] def zariski : DescentTopology := some .zariski

/-- The fpqc topology. -/
@[match_pattern] def fpqc : DescentTopology := none

/-- The fppf topology, viewed as a topology for descent. -/
@[match_pattern] def fppf : DescentTopology := some .fppf

/-- The étale topology, viewed as a topology for descent. -/
@[match_pattern] def etale : DescentTopology := some .etale

/-- The smooth topology, viewed as a topology for descent. -/
@[match_pattern] def smooth : DescentTopology := some .smooth

/-- The syntomic topology, viewed as a topology for descent. -/
@[match_pattern] def syntomic : DescentTopology := some .syntomic

/-- The canonical scheme precoverage associated to a descent topology. -/
def precoverage (τ : DescentTopology) : Precoverage Scheme.{u} :=
  match τ with
  | .zariski => Scheme.zariskiPrecoverage
  | .fpqc => Scheme.fpqcPrecoverage
  | .fppf => Scheme.fppfPrecoverage
  | .etale => Scheme.etalePrecoverage
  | .smooth => Scheme.bigSmoothPrecoverage
  | .syntomic => Scheme.bigSyntomicPrecoverage

/-- Embed the five standard topologies into the six descent topologies. -/
def ofStandard : StandardTopology → DescentTopology
  | .zariski => .zariski
  | .etale => .etale
  | .smooth => .smooth
  | .syntomic => .syntomic
  | .fppf => .fppf

/-- The standard-topology embedding preserves the associated scheme precoverage. -/
theorem precoverageOfStandard (τ : StandardTopology) :
    (ofStandard τ).precoverage = τ.precoverage := sorry

end AlgebraicGeometry.DescentTopology

namespace CategoryTheory.MorphismProperty

open AlgebraicGeometry

/-- A property of scheme morphisms satisfies descent for `τ` when every descent datum on a
`τ`-cover whose component structure morphisms have the property is effective. -/
def SatisfiesDescent
    (P : MorphismProperty Scheme.{u}) (τ : DescentTopology) : Prop :=
  ∀ (S : Scheme.{u}) (𝒰 : Scheme.Cover.{u} τ.precoverage S)
      (D : Scheme.DescentData 𝒰.X 𝒰.f),
    (∀ i, P (D.obj i).hom) → D.IsEffective

/-- A morphism property satisfies descent exactly when every componentwise instance over
every cover has effective descent data. -/
theorem satisfiesDescent_iff
    (P : MorphismProperty Scheme.{u}) (τ : DescentTopology) :
    P.SatisfiesDescent τ ↔
      ∀ (S : Scheme.{u}) (𝒰 : Scheme.Cover.{u} τ.precoverage S)
        (D : Scheme.DescentData 𝒰.X 𝒰.f),
          (∀ i, P (D.obj i).hom) → D.IsEffective := sorry

namespace SatisfiesDescent

/-- Apply descent to a specified cover and componentwise morphism property. -/
theorem effective
    {P : MorphismProperty Scheme.{u}} {τ : DescentTopology}
    (h : P.SatisfiesDescent τ) {S : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} τ.precoverage S) (D : Scheme.DescentData 𝒰.X 𝒰.f)
    (hD : ∀ i, P (D.obj i).hom) : D.IsEffective := sorry

/-- A stronger morphism property inherits descent from a weaker one. -/
theorem of_le
    {P Q : MorphismProperty Scheme.{u}} {τ : DescentTopology}
    (hPQ : P ≤ Q) (hQ : Q.SatisfiesDescent τ) : P.SatisfiesDescent τ := sorry

end SatisfiesDescent

end CategoryTheory.MorphismProperty
