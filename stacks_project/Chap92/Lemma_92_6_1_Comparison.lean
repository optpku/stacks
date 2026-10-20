module

public import ReasLib.AlgebraicGeometry.RingedSite.Cotangent.DerivedBaseChange

open CategoryTheory

universe u

#check (RingedSite.Cotangent.Functoriality.InducesDerivedTensorQuasiIso :
  ∀ {A A' B B' : CommRingCat.{u}} {α : A ⟶ B} {ρ : A ⟶ A'}
    {β : A' ⟶ B'} {φ : B ⟶ B'}, CommSq ρ α β φ → Prop)
