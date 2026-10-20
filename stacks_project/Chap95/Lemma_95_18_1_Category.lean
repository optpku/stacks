module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Basic
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# The category of degree `d` finite Hilbert lifts

The category and its explicit object and morphism constructors are provided by
the mathematical owner of finite Hilbert lifts.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

#check (category : (F : X ⟶ Y) → (d : ℕ) → Cat.{u, u + 1})

#check (Obj.of : {F : X ⟶ Y} → {d : ℕ} → (U Z : Over S) → (π : Z ⟶ U) →
  IsFiniteLocallyFreeOfRank π.left d → (y : Y.p.Fiber U) → (x : X.p.Fiber Z) →
  (restrictObj y π ≅ (fiberFunctor F Z).obj x) → Obj F d)

#check (Hom.homMk : {F : X ⟶ Y} → {d : ℕ} → {ξ ξ' : Obj F d} →
  (f : ξ.U ⟶ ξ'.U) → (g : ξ.Z ⟶ ξ'.Z) → (hfg : ξ.π ≫ f = g ≫ ξ'.π) →
  IsPullback g.left ξ.π.left ξ'.π.left f.left →
  (b : ξ.y ≅ restrictObj ξ'.y f) → (a : ξ.x ≅ restrictObj ξ'.x g) →
  HomCompatible f g hfg b a → Hom ξ ξ')

end AlgebraicGeometry.FiniteHilbertStack
