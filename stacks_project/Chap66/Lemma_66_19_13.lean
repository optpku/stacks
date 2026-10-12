/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Point.TypeImage
public import stacks_project.Chap66.Lemma_66_19_7_Point

/-!
# Points of the small étale topos of an algebraic space

Every point of `Sh(X_étale)` is realized, up to isomorphism of stalk functors, by a geometric
point of the algebraic space `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Lemma 66.19.13: let `S` be a scheme and let `X` be an algebraic space over `S`. Every
point `p : Sh(pt) ⟶ Sh(X_étale)` of the small étale topos of `X` admits a geometric point
`x̄` of `X` such that the stalk functor `F ↦ F_p` is isomorphic to the stalk functor
`F ↦ F_x̄`. Here `p.typeInverseImage` is `F ↦ F_p`, and
`(toSmallEtalePoint xbar).sheafFiber` is `F ↦ F_x̄` via `stalkFunctor` and
`toSmallEtalePoint_stalkIso`. -/
@[stacks 04K6]
theorem exists_iso_stalkFunctor
    (p : MorphismOfTopoiIn (smallEtaleTopology X) typesGrothendieckTopology.{u + 1}) :
    ∃ xbar : GeometricPoint X,
      Nonempty
        (p.typeInverseImage ≅
          ((toSmallEtalePoint xbar).sheafFiber :
            Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ Type (u + 1))) :=
  sorry

/-- Every point of the small étale site of an algebraic space `X` is isomorphic, as a fiber
functor, to the site-point `toSmallEtalePoint xbar` of some geometric point of `X`. -/
theorem exists_iso_toSmallEtalePoint (p : (smallEtaleTopology X).Point.{u}) :
    ∃ xbar : GeometricPoint X,
      Nonempty (p.fiber ≅ (toSmallEtalePoint xbar).fiber) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
