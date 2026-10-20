module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SurjectiveOnObjects

/-!
# 1-morphisms of groupoid fibrations that are surjective on objects

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is surjective
on objects when every object of the target over the spectrum of a field lifts
after a field extension over `S`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

#check
  (AlgebraicGeometry.Groupoids.Hom.SurjectiveOnObjects.pullback_fst :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y)
      [AlgebraicGeometry.Groupoids.Hom.SurjectiveOnObjects f],
      AlgebraicGeometry.Groupoids.Hom.SurjectiveOnObjects
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f))
