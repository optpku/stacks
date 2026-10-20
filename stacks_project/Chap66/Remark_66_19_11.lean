module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.Stalk
import StacksCheckRecall

/-!
# Independence of geometric points over a point of an algebraic space

The pullback presentation of the small-étale stalk functor at a geometric point of an
algebraic space depends only on the underlying point of `|X|`.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Remark 66.19.11: let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`x` be a point of `|X|`. For any pair of geometric points `p` and `q` of `X` lying over `x`,
the stalk functors `Sh(X_étale) ⥤ Type` given by pullback along `p.hom` and along `q.hom`
are isomorphic.

By definition of `|X|` there is a third geometric point `p''` together with a commutative
triangle `p'' ⟶ p`, `p'' ⟶ q`, both over `X`. Since the stalk functor is pullback along the
geometric-point morphism, functoriality of pullback yields the isomorphism. -/
@[stacks 04K4] #check
  (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.pullbackStalkFunctors_isomorphic :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → (x : Points X) →
      (p q : FieldValuedPoint X) → [IsAlgClosed p.K] → [IsAlgClosed q.K] →
      (hp : Points.mk p = x) → (hq : Points.mk q = x) →
      [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
        (etaleBaseChange p.hom).op.HasLeftKanExtension F] →
      [HasWeakSheafify (spacesEtaleTopology (ofOver p.overObj)) (Type (u + 1))] →
      [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
        (etaleBaseChange q.hom).op.HasLeftKanExtension F] →
      [HasWeakSheafify (spacesEtaleTopology (ofOver q.overObj)) (Type (u + 1))] →
      Nonempty (p.pullbackStalkFunctor ≅ q.pullbackStalkFunctor))
