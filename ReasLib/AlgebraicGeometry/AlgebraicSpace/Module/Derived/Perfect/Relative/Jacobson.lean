module

public import Mathlib.RingTheory.Jacobson.Ring
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SpecialFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- A pseudo-coherent derived module on a proper, flat, finitely presented algebraic
space over `Spec R` is relatively perfect if its derived restriction to the quotient
fibre over `Spec (R ⧸ I)` is relatively perfect and `I ≤ Ring.jacobson R`. -/
theorem isPerfectRelativeTo_of_quotient_of_le_jacobson
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    [Proper f] [Flat f] [FinitePresentation f]
    (E : ModuleDerived X) (hE : IsPseudoCoherent X E)
    (hE₀ : IsPerfectRelativeTo (Limits.pullback.snd f (specQuotientι I))
      ((pullback (Limits.pullback.fst f (specQuotientι I))).obj E)) :
    IsPerfectRelativeTo f E := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
