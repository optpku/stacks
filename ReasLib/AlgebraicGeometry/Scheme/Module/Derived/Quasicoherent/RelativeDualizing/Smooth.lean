/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.DifferentialExterior

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a smooth proper morphism of relative dimension `d` over a Noetherian scheme,
the shifted top exterior power of relative differentials is isomorphic to its relative
dualizing complex. -/
theorem differentialExteriorShift_isomorphic_relativeDualizingComplex
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsProper f]
    (a : DerivedQCoh S ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a) :
    IsIsomorphic (Scheme.Hom.differentialExteriorShift f d)
      (relativeDualizingComplex f a aAdjunction) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
