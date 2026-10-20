module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Points
import StacksCheckRecall

/-!
# Points of the small étale topos of an algebraic space

Every point of `Sh(X_étale)` is realized, up to isomorphism of stalk functors, by a geometric
point of the algebraic space `X`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

/- Lemma 66.19.13: let `S` be a scheme and let `X` be an algebraic space over `S`. Every
point `p : Sh(pt) ⟶ Sh(X_étale)` of the small étale topos of `X` admits a geometric point
`x̄` of `X` such that the stalk functor `F ↦ F_p` is isomorphic to the stalk functor
`F ↦ F_x̄`. Here `p.typeInverseImage` is `F ↦ F_p`, and
`(toSmallEtalePoint xbar).sheafFiber` is `F ↦ F_x̄` via `stalkFunctor` and
`toSmallEtalePoint_stalkIso`. -/
@[stacks 04K6] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.exists_iso_stalkFunctor :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (p : MorphismOfTopoiIn (smallEtaleTopology X) typesGrothendieckTopology.{u + 1}),
    ∃ xbar : GeometricPoint X,
      Nonempty
        (p.typeInverseImage ≅
          ((toSmallEtalePoint xbar).sheafFiber :
            Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ Type (u + 1))))

#check (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.exists_iso_toSmallEtalePoint :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (p : (smallEtaleTopology X).Point.{u}),
    ∃ xbar : GeometricPoint X,
      Nonempty (p.fiber ≅ (toSmallEtalePoint xbar).fiber))

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
