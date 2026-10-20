module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Algebraic
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Definition 97.8.1: a 1-morphism `F : X ⟶ Y` of stacks in groupoids over
`(Sch/S)_fppf` is algebraic if for every scheme `T` over `S` and every object
`ξ` of `Y` over `T` the 2-fibre product `(Sch/T)_fppf ×_{ξ, Y} X` is an
algebraic stack over `S`. -/
@[stacks 06CF] #check (AlgebraicGeometry.Groupoids.Hom.Algebraic :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.Groupoids.Hom.Algebraic.iff_yonedaRepresentative :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y),
    Groupoids.Hom.Algebraic F ↔
      ∀ (T : Over S) (ξ : Y.p.Fiber T),
        AlgebraicStack
          (TwoFibreProduct.apex.{u + 1, u, u + 1, u}
            (YonedaSlice.representative ξ) F))
