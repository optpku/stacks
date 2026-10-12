/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Points
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

@[expose] public section

universe u

/- Lemma 59.29.12 (1): every point of the small étale site of a scheme is represented
by a geometric point, up to an isomorphism of fiber functors. -/
@[stacks 04HU] #check (AlgebraicGeometry.Scheme.GeometricPoint.exists_iso_toSmallEtalePoint :
    ∀ {S : Scheme.{u}} (p : (Scheme.smallEtaleTopology S).Point),
      ∃ s : Scheme.GeometricPoint S,
        Nonempty (p.fiber ≅ (Scheme.GeometricPoint.toSmallEtalePoint s).fiber))

/- Lemma 59.29.12 (2): every point of the small étale topos of a scheme has inverse
image naturally isomorphic to the sheaf stalk functor at a geometric point. -/
@[stacks 04HU] #check (AlgebraicGeometry.Scheme.Etale.exists_iso_stalkFunctor :
    ∀ {S : Scheme.{u}}
      (p : MorphismOfTopoiIn (Scheme.smallEtaleTopology S) typesGrothendieckTopology.{u + 1}),
      ∃ s : Scheme.GeometricPoint S,
        Nonempty (p.typeInverseImage ≅
          ((Scheme.GeometricPoint.toSmallEtalePoint s).sheafFiber :
            Sheaf (Scheme.smallEtaleTopology S) (Type (u + 1)) ⥤ Type (u + 1))))
