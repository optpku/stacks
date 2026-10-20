/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.PolynomialAugmentation
import StacksCheckRecall

@[expose] public section

universe u

/- 92.4.0.1 (1): the morphism of ringed topoi i : (Sh(C), underline{B}) ⟶ (Sh(C), O)
is the identity on underlying topoi, with i♯ : O ⟶ underline{B} the augmentations. -/
@[stacks 08PR]
#check (CommAlgCat.Over.Polynomial.Site.i :
  (A B : Type u) → [CommRing A] → [CommRing B] → [Algebra A B] →
    RingedSite.ToposHom (CommAlgCat.Over.Polynomial.Site.constantRingedSite A B)
      (CommAlgCat.Over.Polynomial.Site.ringedSite A B))

/- 92.4.0.1 (2): the morphism of ringed topoi π : (Sh(C), underline{B}) ⟶ (Sh(*), B)
is the category-to-point morphism. -/
@[stacks 08PR]
#check (CommAlgCat.Over.Polynomial.Site.toPoint :
  (A B : Type u) → [CommRing A] → [CommRing B] → [Algebra A B] →
    RingedSite.ToposHom (CommAlgCat.Over.Polynomial.Site.constantRingedSite A B)
      (CommAlgCat.Over.Polynomial.Site.pointRingedSite B))
