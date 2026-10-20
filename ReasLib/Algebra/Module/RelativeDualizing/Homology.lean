module

public import ReasLib.Algebra.Module.RelativeDualizing
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.Finite
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.OpenImmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.ModuleCat.UpperShriek

noncomputable section

universe u

namespace Algebra.RelativeDualizingModule

/-- For a quasi-finite homomorphism of Noetherian rings, the relative dualizing
module from a finite/open model is isomorphic to degree-zero homology of the
associated presentation-defined upper-shriek complex. -/
theorem isomorphicHomologyZero
    (A B' B : Type u) [CommRing A] [CommRing B'] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B) [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (p : Presentation (algebraMap A B)) :
    IsIsomorphic (of A B' B h_quasiFinite h_open)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u, u} B) 0).obj
        (p.functor.obj (ModuleCat.single0 (ModuleCat.of A A)))) := sorry

end Algebra.RelativeDualizingModule
