module

public import Mathlib.Logic.Relation
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap83.Definition_83_4_1_Invariant
public import stacks_project.Chap83.Definition_83_5_13_SetTheoretic
public import stacks_project.Chap83.Lemma_83_5_6_Generated

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open _root_.Relation (EqvGen)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
variable (P : PreRelation U)

/-- Lemma 83.5.6 (1): for a pre-relation `j : R ⟶ U ⨯ U` over `B`, the generated
pre-relation `j_∞ : R_∞ ⟶ U ⨯ U` is a pre-equivalence relation over `B`. -/
@[stacks 048T]
theorem generated_isPreEquivalence : P.generated.IsPreEquivalence := sorry

/-- Lemma 83.5.6 (2): a morphism `φ : U ⟶ X` over `B` is `R`-invariant if and only if
it is `R_∞`-invariant. -/
@[stacks 048T]
theorem equalizes_iff_generated {X : Over B} (φ : U ⟶ X) :
    P.IsInvariant φ ↔ P.generated.IsInvariant φ := sorry

/-- Lemma 83.5.6 (3): the canonical map of fppf quotient sheaves `U/R ⟶ U/R_∞` on
`Spaces / B` is an isomorphism. -/
@[stacks 048T]
theorem generated_spacesQuotientMap_isIso : IsIso P.generated_spacesQuotientMap := sorry

/-- Lemma 83.5.6 (4): weak `R`-orbits of geometric `k`-points of `U` agree with weak
`R_∞`-orbits. -/
@[stacks 048T]
theorem generated_eqvGen_pointRel (k : GeometricPoint B) (x y : Over.mk k.hom ⟶ U) :
    EqvGen (P.pointRel (Over.mk k.hom)) x y ↔
      EqvGen (P.generated.pointRel (Over.mk k.hom)) x y := sorry

/-- Lemma 83.5.6 (5): `R`-orbits of geometric `k`-points of `U` agree with `R_∞`-orbits,
after restriction along a field extension of `k`. -/
@[stacks 048T]
theorem generated_orbitRel (k : GeometricPoint B) (x y : Over.mk k.hom ⟶ U) :
    (∃ (L : Type u) (_ : Field L) (_ : Algebra k.K L),
        EqvGen (P.pointRel (Over.mk (fieldExtensionOverMap L k.structureHom ≫ k.hom)))
          (restrictAlongFieldExtension L x) (restrictAlongFieldExtension L y)) ↔
      (∃ (L : Type u) (_ : Field L) (_ : Algebra k.K L),
        EqvGen (P.generated.pointRel
            (Over.mk (fieldExtensionOverMap L k.structureHom ≫ k.hom)))
          (restrictAlongFieldExtension L x) (restrictAlongFieldExtension L y)) := sorry

/-- Lemma 83.5.6 (6): if `s` and `t` are locally of finite type, then so are `s_∞` and
`t_∞`. -/
@[stacks 048T]
theorem generated_locallyOfFiniteType
    [LocallyOfFiniteType P.s.left] [LocallyOfFiniteType P.t.left] :
    LocallyOfFiniteType (s (generated P)).left ∧
      LocallyOfFiniteType (t (generated P)).left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
