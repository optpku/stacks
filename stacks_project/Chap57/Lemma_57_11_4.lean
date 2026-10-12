/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Cohomology.Stalk
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.RingedSpace.Module.Skyscraper
open CategoryTheory.DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

/- Lemma 57.11.4: for a bounded coherent derived module on a Noetherian scheme, vanishing
of all cohomology stalks above `b` is equivalent to vanishing of all morphisms to the
correspondingly shifted residue-field skyscraper sheaves. -/
@[stacks 0GWZ] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.cohomologyStalk_isZero_iff_hom_isZero :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      (x : X) (hx : x ∈ closedPoints X)
      (K : Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]) (b : ℤ),
    let E := (ambient (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).obj K
    let kx : ModuleCat (RingCat.of (X.presheaf.stalk x)) :=
      ModuleCat.of (RingCat.of (X.presheaf.stalk x))
        (IsLocalRing.ResidueField (X.presheaf.stalk x))
    let Ox := atPoint x kx
    (∀ i : ℤ, b < i → IsZero (cohomologyStalk E i x)) ↔
      ∀ i : ℤ, b < i →
        ∀ f : E ⟶
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj Ox)⟦(-i : ℤ)⟧,
          f = 0)
