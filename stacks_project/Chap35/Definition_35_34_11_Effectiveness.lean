module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity

/-!
# Effective scheme descent data

This compatibility module reexports the reusable definition and basic API for
effective scheme descent data.
-/

open CategoryTheory

universe u v

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

#check (@AlgebraicGeometry.Scheme.DescentData.IsEffective.ofObj :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
    {X : I → AlgebraicGeometry.Scheme.{u}} {f : ∀ i, X i ⟶ S}
    (U : Over S),
      AlgebraicGeometry.Scheme.DescentData.IsEffective
        (AlgebraicGeometry.Scheme.DescentData.ofObj X f U))

#check (@AlgebraicGeometry.Scheme.DescentData.IsEffective.ofIso :
  ∀ {I : Type v} {S : AlgebraicGeometry.Scheme.{u}}
    {X : I → AlgebraicGeometry.Scheme.{u}} {f : ∀ i, X i ⟶ S}
    {D E : AlgebraicGeometry.Scheme.DescentData X f},
      (D ≅ E) → AlgebraicGeometry.Scheme.DescentData.IsEffective D →
      AlgebraicGeometry.Scheme.DescentData.IsEffective E)
