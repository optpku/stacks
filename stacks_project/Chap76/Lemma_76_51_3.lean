/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Chow.Derived.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.51.3. Let `X` over `A`, `x ∈ Points X`, and `n`, `Z`, `z`, `V`, `E`
be as in Lemma 76.51.2. For any `K` in `DerivedQCoh X` there is a canonical
identification `fourierMukaiRestrict M K ≅ closedImmersionPushforward M K`
in `ModuleDerived V.X`, where `p = ProjectiveSpace.toBase M.n X` and
`q = ProjectiveSpace.toOfScheme M.n X` are the projections and `W ⟶ V` is the
finitely presented closed immersion `c|_W = M.preimageTo`. -/
@[stacks 0CTS] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedChowPresentation.fourierMukaiRestrict_iso :
    ∀ {A : Type u} [CommRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [Separated (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase X)]
      {x : Points X} (M : DerivedChowPresentation x) (K : DerivedQCoh X),
      DerivedChowPresentation.fourierMukaiRestrict M K ≅
        DerivedChowPresentation.closedImmersionPushforward M K)
