module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.PlusModel

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek

/-- For an etale morphism of finite-type separated schemes over a Noetherian
base, the bounded-below upper-shriek functor associated to a compactification
and right-adjoint model is isomorphic to bounded-below derived pullback. -/
theorem isomorphic_pullback_of_etale
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) [Etale f.hom.left]
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint
      (AlgebraicGeometry.Scheme.Compactification.Of.ambientMorphism P)) :
    IsIsomorphic (upperShriek f P A.plus)
      (DerivedQCoh.Flat.pullbackPlus f.hom.left) := sorry

end AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek
