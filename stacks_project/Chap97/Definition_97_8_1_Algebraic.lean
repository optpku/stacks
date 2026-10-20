module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Algebraic

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Algebraic morphisms of groupoid fibrations

A 1-morphism of stacks in groupoids over `(Sch/S)_fppf` is algebraic when every
slice 2-fibre product against an object of the target is an algebraic stack
over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

#check (AlgebraicGeometry.Groupoids.Hom.Algebraic :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}, (X ⟶ Y) → Prop)

namespace Algebraic

#check (AlgebraicGeometry.Groupoids.Hom.Algebraic.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}, Algebraic (𝟙 X))

#check (AlgebraicGeometry.Groupoids.Hom.Algebraic.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y) [Algebraic F]
    {T : Over S} (ξ : GroupoidsOver.slice T ⟶ Y),
    AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} ξ F))

#check (AlgebraicGeometry.Groupoids.Hom.Algebraic.iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y),
    Algebraic F ↔
      ∀ ⦃T : Over S⦄ (ξ : GroupoidsOver.slice T ⟶ Y),
        AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} ξ F))

#check (AlgebraicGeometry.Groupoids.Hom.Algebraic.iff_yonedaRepresentative :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (F : X ⟶ Y),
    Algebraic F ↔
      ∀ (T : Over S) (ξ : Y.p.Fiber T),
        AlgebraicStack
          (TwoFibreProduct.apex.{u + 1, u, u + 1, u}
            (YonedaSlice.representative ξ) F))

end Algebraic

end AlgebraicGeometry.Groupoids.Hom
