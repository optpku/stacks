module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage.ChosenSite

/-!
# Chosen big sites of algebraic spaces

The canonical chosen-site API and its étale specialization are available from
the shared mathematical library.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Cardinal

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigSite :
  ∀ {S : Scheme.{u}}, Precoverage (AlgebraicSpace S) → Type (u + 2))

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.ofBound :
  ∀ {S : Scheme.{u}} {P : Precoverage (AlgebraicSpace S)} (κ : Cardinal.{u + 1}),
    (P.restrictCardinalLE κ).IsSite →
    P.coversUpToCombinatorialEquivalence (P.restrictCardinalLE κ) →
    AlgebraicSpace.ChosenBigSite P)

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.ofBound_bound :
  ∀ {S : Scheme.{u}} {P : Precoverage (AlgebraicSpace S)} (κ : Cardinal.{u + 1})
    (h_site : (P.restrictCardinalLE κ).IsSite)
    (h_equiv : P.coversUpToCombinatorialEquivalence (P.restrictCardinalLE κ)),
    (AlgebraicSpace.ChosenBigSite.ofBound κ h_site h_equiv).bound = κ)

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.precoverage :
  ∀ {S : Scheme.{u}} {P : Precoverage (AlgebraicSpace S)},
    AlgebraicSpace.ChosenBigSite P → Precoverage (AlgebraicSpace S))

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.toGrothendieck :
  ∀ {S : Scheme.{u}} {P : Precoverage (AlgebraicSpace S)},
    AlgebraicSpace.ChosenBigSite P → GrothendieckTopology (AlgebraicSpace S))

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.spec :
  ∀ {S : Scheme.{u}} {P : Precoverage (AlgebraicSpace S)}
    (X : AlgebraicSpace.ChosenBigSite P),
    X.precoverage = P.restrictCardinalLE X.bound ∧
      (P.restrictCardinalLE X.bound).IsSite ∧
      P.coversUpToCombinatorialEquivalence (P.restrictCardinalLE X.bound))

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.mem_precoverage_iff :
  ∀ {S : Scheme.{u}} {P : Precoverage (AlgebraicSpace S)}
    (X : AlgebraicSpace.ChosenBigSite P) {Y : AlgebraicSpace S} {R : Presieve Y},
    R ∈ X.precoverage Y ↔
      R ∈ P Y ∧ Cardinal.lift #(R.uncurry) ≤ Cardinal.lift X.bound)

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.toGrothendieck_eq :
  ∀ {S : Scheme.{u}} {P : Precoverage (AlgebraicSpace S)}
    (X : AlgebraicSpace.ChosenBigSite P), X.toGrothendieck = P.toGrothendieck)

#check (AlgebraicGeometry.AlgebraicSpace.etalePrecoverage.instIsSite :
  ∀ {S : Scheme.{u}},
    (AlgebraicSpace.etalePrecoverage : Precoverage (AlgebraicSpace S)).IsSite)

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigEtaleSite : Scheme.{u} → Type (u + 2))

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigEtaleSite.exists :
  ∀ (S : Scheme.{u}), Nonempty (AlgebraicSpace.ChosenBigEtaleSite S))
