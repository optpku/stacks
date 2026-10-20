module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.Morphism

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- The canonical locally-finite-type instance for morphisms in `FiniteTypeSeparatedOver`. -/
#check (AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver.instLocallyOfFiniteTypeHom :
  ∀ {S : Scheme.{u}} [IsNoetherian S]
    {X Y : AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y),
    LocallyOfFiniteType f.hom.left)
