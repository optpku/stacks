module

public import stacks_project.Chap83.Definition_83_5_4_Orbit

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}

/-- Lemma 83.5.5 (1): if `P` is a pre-equivalence relation over `B` and `bbar` is a geometric
point of `B`, then the weak orbit of `u` is the set of `u'` for which there exists
`r : Over.mk bbar.hom ⟶ P.left` with `r ≫ P.s = u` and `r ≫ P.t = u'`. -/
@[stacks 048R]
theorem weakOrbit_eq_of_isPreEquivalence (P : PreRelation U) (hP : P.IsPreEquivalence)
    (bbar : GeometricPoint B) (u : Over.mk bbar.hom ⟶ U) :
    P.weakOrbit (Over.mk bbar.hom) u =
      {u' | ∃ r : Over.mk bbar.hom ⟶ P.left, r ≫ P.s = u ∧ r ≫ P.t = u'} :=
  sorry

/-- Lemma 83.5.5 (2): if `P` is a pre-equivalence relation over `B` and `bbar` is a geometric
point of `B`, then the orbit of `u` is the set of `u'` for which there exist a field-valued
point `q` of `B` factoring through `bbar` and `r : Over.mk q.hom ⟶ P.left` with `r ≫ P.s`
and `r ≫ P.t` equal to the images of `u` and `u'` along `φ.sliceHom`. -/
@[stacks 048R]
theorem orbit_eq_of_isPreEquivalence (P : PreRelation U) (hP : P.IsPreEquivalence)
    (bbar : GeometricPoint B) (u : Over.mk bbar.hom ⟶ U) :
    P.orbit bbar u =
      {u' | ∃ (q : FieldValuedPoint B)
          (φ : FieldValuedPoint.Factorization q bbar.toFieldValuedPoint)
          (r : Over.mk q.hom ⟶ P.left),
        r ≫ P.s = φ.sliceHom ≫ u ∧ r ≫ P.t = φ.sliceHom ≫ u'} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
