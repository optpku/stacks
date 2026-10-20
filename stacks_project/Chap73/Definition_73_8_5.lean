module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PhPrecoverage.ChosenSite
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Definition 73.8.5: let `S` be a scheme. A big ph site `(Spaces / S)_ph`
is constructed by choosing a big ph scheme site, taking algebraic spaces over
`S`, and selecting a set of ph coverings as in Sets Lemma 3.11.1. This
formalization works in the fixed-universe category `AlgebraicSpace S` and
presents covering families by their presieves of arrows. A value of
`ChosenBigPhSite S` stores a cardinal bound whose truncation of `phPrecoverage`
is a site and combinatorially represents every ambient ph covering, as exposed
by `ChosenBigSite.spec`. It does not store a chosen scheme-site datum or the
original indexed-family codes and their rank bounds. -/
@[stacks 0DFK] #check (AlgebraicGeometry.AlgebraicSpace.ChosenBigPhSite :
    AlgebraicGeometry.Scheme.{u} → Type (u + 2))

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.ofBound :
    ∀ {S : Scheme.{u}} {P : Precoverage (AlgebraicSpace S)} (κ : Cardinal.{u + 1}),
      (P.restrictCardinalLE κ).IsSite →
      P.coversUpToCombinatorialEquivalence (P.restrictCardinalLE κ) →
      AlgebraicSpace.ChosenBigSite P)

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigSite.spec :
    ∀ {S : Scheme.{u}} {P : Precoverage (AlgebraicSpace S)}
      (X : AlgebraicSpace.ChosenBigSite P),
      X.precoverage = P.restrictCardinalLE X.bound ∧
        (P.restrictCardinalLE X.bound).IsSite ∧
        P.coversUpToCombinatorialEquivalence (P.restrictCardinalLE X.bound))

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigPhSite.exists :
    ∀ S : Scheme.{u}, Nonempty (AlgebraicSpace.ChosenBigPhSite S))

#check (AlgebraicGeometry.AlgebraicSpace.phPrecoverage :
    ∀ {S : Scheme.{u}}, Precoverage (AlgebraicSpace S))
