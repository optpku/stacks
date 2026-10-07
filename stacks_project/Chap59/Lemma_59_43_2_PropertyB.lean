module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PropertyB

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty
open CategoryTheory.Limits

universe u

#check (AlgebraicGeometry.hasPropertyB :
  ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → Prop)
