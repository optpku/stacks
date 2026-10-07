module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- The shared owner supplies the canonical derived pullback for every scheme morphism. -/
#check (@AlgebraicGeometry.Scheme.DerivedQCoh.pullback.{u} :
  ∀ {X U : Scheme.{u}}, (U ⟶ X) → DerivedQCoh X ⥤ DerivedQCoh U)

end AlgebraicGeometry.Scheme.DerivedQCoh
