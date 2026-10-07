module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Unramified
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

open AlgebraicGeometry
open AlgebraicGeometry.Scheme

/- Lemma 39.3.5: An unramified pre-relation whose relation on every algebraically closed
field-valued point is an equivalence relation, and whose explicit identity, inverse, and
composition morphisms satisfy the endpoint equations, is an internal equivalence relation. -/
@[stacks 0DT7] #check
  (AlgebraicGeometry.Scheme.PreRelation.isEquivalenceRelation_of_unramified :
    ∀ {S : Scheme.{u}} {U : Over S} (P : PreRelation U)
      [Unramified P.t.left] [Unramified P.s.left]
      (h_points : ∀ (p : FieldValuedPoint S) [IsAlgClosed p.K],
        Function.Injective (P.pointMap p.over) ∧ Equivalence (P.pointRel p.over))
      (e : U ⟶ P.left) (i : P.left ⟶ P.left) (c : pullback P.s P.t ⟶ P.left)
      (e_t : e ≫ P.t = 𝟙 U) (e_s : e ≫ P.s = 𝟙 U)
      (i_t : i ≫ P.t = P.s) (i_s : i ≫ P.s = P.t)
      (c_t : c ≫ P.t = pullback.fst P.s P.t ≫ P.t)
      (c_s : c ≫ P.s = pullback.snd P.s P.t ≫ P.s),
      IsEquivalenceRelation P.t P.s)
