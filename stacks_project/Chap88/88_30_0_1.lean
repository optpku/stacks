module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Affine
import StacksCheckRecall

@[expose] public section

universe u

/- 88.30.0.1 For a Noetherian ring A and ideal I, with X = Spec(A) and
U = X \ V(I), the category of morphisms f : X' ⟶ X of algebraic spaces that
are locally of finite type and such that f⁻¹(U) ⟶ U is an isomorphism.
Morphisms X'/X ⟶ X''/X are morphisms of algebraic spaces over X. -/
@[stacks 0AS2] #check (AlgebraicGeometry.AlgebraicSpace.SpecComplement :
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A], Ideal A → Type (u + 1))
