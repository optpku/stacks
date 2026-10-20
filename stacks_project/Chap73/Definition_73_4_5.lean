/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap73.Definition_73_4_5_Site
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 73.4.5: let `S` be a scheme. A big étale site `(Spaces / S)_étale`
is any site constructed as follows: choosing a big étale site `(Sch / S)_étale`
is recorded by the universe of `Scheme` and `AlgebraicSpace S`; the underlying
category is `AlgebraicSpace S`; the coverings are a set of étale covering
families chosen by a cardinal truncation of
`etalePrecoverage`, i.e. a value of `ChosenBigEtaleSite S`. -/
@[stacks 0DBX] #check (AlgebraicGeometry.AlgebraicSpace.ChosenBigEtaleSite :
  Scheme.{u} → Type (u + 2))

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

#check (AlgebraicGeometry.AlgebraicSpace.ChosenBigEtaleSite.exists :
  ∀ (S : Scheme.{u}), Nonempty (AlgebraicSpace.ChosenBigEtaleSite S))
