/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism

/-!
# Pair groupoids of schemes

This module constructs the pair groupoid on a scheme over a fixed base and the canonical
morphism from any groupoid scheme to the pair groupoid on its object scheme.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Composition in the pair groupoid sends a composable pair of arrows to its outer pair. -/
noncomputable def pairComposition {S : Scheme.{u}} (U : Over S) :
    pullback (prod.snd : U ⨯ U ⟶ U) (prod.fst : U ⨯ U ⟶ U) ⟶ U ⨯ U :=
  prod.lift (pullback.fst _ _ ≫ prod.fst) (pullback.snd _ _ ≫ prod.snd)

/-- The pair groupoid on a scheme `U` over `S`. Its arrows are pairs of objects. -/
noncomputable def pair {S : Scheme.{u}} (U : Over S) : GroupoidScheme S where
  U := U
  R := U ⨯ U
  s := prod.snd
  t := prod.fst
  c := pairComposition U
  e := diag U
  i := prod.lift prod.snd prod.fst
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- The object scheme of the pair groupoid is `U`. -/
theorem pair_U {S : Scheme.{u}} (U : Over S) : (pair U).U = U := sorry

/-- The arrow scheme of the pair groupoid is `U ⨯ U`. -/
theorem pair_R {S : Scheme.{u}} (U : Over S) : (pair U).R = (U ⨯ U) := sorry

/-- The source map of the pair groupoid is the second projection. -/
theorem pair_s {S : Scheme.{u}} (U : Over S) :
    (pair U).s = (prod.snd : U ⨯ U ⟶ U) := sorry

/-- The target map of the pair groupoid is the first projection. -/
theorem pair_t {S : Scheme.{u}} (U : Over S) :
    (pair U).t = (prod.fst : U ⨯ U ⟶ U) := sorry

/-- Composition in the pair groupoid is the outer-pair map. -/
theorem pair_c {S : Scheme.{u}} (U : Over S) :
    (pair U).c = pairComposition U := sorry

/-- The identity map of the pair groupoid is the diagonal. -/
theorem pair_e {S : Scheme.{u}} (U : Over S) : (pair U).e = diag U := sorry

/-- Inversion in the pair groupoid swaps the two factors. -/
theorem pair_i {S : Scheme.{u}} (U : Over S) :
    (pair U).i = prod.lift (prod.snd : U ⨯ U ⟶ U) prod.fst := sorry

/-- The canonical morphism from a groupoid scheme to the pair groupoid on its objects. -/
noncomputable def toPair {S : Scheme.{u}} (G : GroupoidScheme S) : Hom G (pair G.U) where
  obj := 𝟙 G.U
  arrow := G.toPreRelation.hom
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of the canonical morphism to the pair groupoid is the identity. -/
theorem toPair_obj {S : Scheme.{u}} (G : GroupoidScheme S) :
    (toPair G).obj = 𝟙 G.U := sorry

/-- The arrow component of the canonical morphism to the pair groupoid is `(t, s)`. -/
theorem toPair_arrow {S : Scheme.{u}} (G : GroupoidScheme S) :
    (toPair G).arrow = G.toPreRelation.hom := sorry

/-- The object scheme of `G` agrees with that of its pair groupoid. -/
theorem toPair_object_eq {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.U = (pair G.U).U := sorry

/-- The canonical morphism to the pair groupoid is identity on objects. -/
theorem toPair_isIdentityOnObjects {S : Scheme.{u}} (G : GroupoidScheme S) :
    (toPair G).IsIdentityOnObjects (toPair_object_eq G) := sorry

end AlgebraicGeometry.GroupoidScheme
