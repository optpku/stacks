module

public import ReasLib.AlgebraicGeometry.LocalizedChern.DerivedEnvelopeCaps
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Reanchor
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Representative.LocallyFree.Pullback
public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern.EnvelopeCaps

/-- Existence of an envelope with a locally bounded finite locally free representative
is preserved by derived pullback along a morphism of schemes. -/
theorem defined_pullback {X X' : Scheme.{u}} (h : X' ⟶ X)
    (Q : RingedSpace.ModuleDerived X.toRingedSpace)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q)) :
    ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ X'), IsEnvelope f' ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f'.toShHom).obj
          ((RingedSpace.modulePullbackDerived h.toShHom).obj Q)) := sorry

/-- The envelope-descended Newton and Chern operations commute with locally finite-type
restriction, using the pulled-back complex and the reanchored Chern-class theory. -/
theorem derivedClass_restrict
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (h : X' ⟶ X) [LocallyOfFiniteType h.left]
    (classes : ChernClass.Theory δ X.hom)
    (Q : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect Q)
    (defined : ∃ (Y : Scheme.{u}) (f : Y ⟶ X.left), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj Q))
    (rankBound : Bool) (p : ℕ) :
    derivedClass δ (classes.reanchor X')
        ((RingedSpace.modulePullbackDerived h.left.toShHom).obj Q)
        (RingedSpace.modulePullbackDerived_isPerfect h.left.toShHom Q perfect)
        (defined_pullback h.left Q defined) rankBound p =
      BivariantClass.restrict δ h (𝟙 X') h IsPullback.of_id_snd (p : ℤ)
        (derivedClass δ classes Q perfect defined rankBound p) := sorry

end AlgebraicGeometry.LocalizedChern.EnvelopeCaps
