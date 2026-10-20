module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf

/-!
# Presheaf functors of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.forgetToPresheaf :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S ⥤ ((Over S)ᵒᵖ ⥤ Type u))
