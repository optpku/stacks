module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Cohomology.Proper
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 50.3.4: if `A` is Noetherian and `p : X ⟶ Spec A` is proper, then every relative
de Rham cohomology module `Hⁱ_dR(X / Spec A)` is finite over `A`. -/
@[stacks 0FLZ] #check
  (AlgebraicGeometry.Scheme.DeRham.cohomologyFinite :
    ∀ {A : CommRingCat.{u}} [IsNoetherianRing A] {X : Scheme.{u}}
      (p : X ⟶ Spec A) [IsProper p] (i : ℤ),
      Module.Finite A (AlgebraicGeometry.Scheme.DeRham.cohomologyOverAffineBase p i))
