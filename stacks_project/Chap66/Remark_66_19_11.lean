module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import stacks_project.Chap66.Remark_66_19_11_StalkFunctor

/-!
# Independence of geometric points over a point of an algebraic space

The pullback presentation of the small-étale stalk functor at a geometric point of an
algebraic space depends only on the underlying point of `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Remark 66.19.11: let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`x` be a point of `|X|`. For any pair of geometric points `p` and `q` of `X` lying over `x`,
the stalk functors `Sh(X_étale) ⥤ Type` given by pullback along `p.hom` and along `q.hom`
are isomorphic.

By definition of `|X|` there is a third geometric point `p''` together with a commutative
triangle `p'' ⟶ p`, `p'' ⟶ q`, both over `X`. Since the stalk functor is pullback along the
geometric-point morphism, functoriality of pullback yields the isomorphism. -/
@[stacks 04K4]
theorem pullbackStalkFunctors_isomorphic (x : Points X) (p q : FieldValuedPoint X)
    [IsAlgClosed p.K] [IsAlgClosed q.K] (hp : Points.mk p = x) (hq : Points.mk q = x)
    [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange p.hom).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology (ofOver p.overObj)) (Type (u + 1))]
    [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange q.hom).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology (ofOver q.overObj)) (Type (u + 1))] :
    Nonempty (p.pullbackStalkFunctor ≅ q.pullbackStalkFunctor) := sorry

/-- Geometric points with the same image in `|X|` admit a common geometric extension. -/
theorem exists_geometric_commonExtension (p q : FieldValuedPoint X)
    [IsAlgClosed p.K] [IsAlgClosed q.K] (h : Points.mk p = Points.mk q) :
    ∃ e : CommonExtension p q, IsAlgClosed e.point.K := sorry

/-- A factorization of geometric points induces an isomorphism of pullback-stalk functors. -/
theorem pullbackStalkFunctor_iso_of_factorization {p q : FieldValuedPoint X}
    [IsAlgClosed p.K] [IsAlgClosed q.K] (φ : Factorization p q)
    [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange p.hom).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology (ofOver p.overObj)) (Type (u + 1))]
    [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
      (etaleBaseChange q.hom).op.HasLeftKanExtension F]
    [HasWeakSheafify (spacesEtaleTopology (ofOver q.overObj)) (Type (u + 1))] :
    Nonempty (p.pullbackStalkFunctor ≅ q.pullbackStalkFunctor) := sorry

end AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint
