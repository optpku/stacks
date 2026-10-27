/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
  comp_source := prod.lift_snd _ _
  comp_target := prod.lift_fst _ _
  identity_source := prod.lift_snd _ _
  identity_target := prod.lift_fst _ _
  inverse_source := prod.lift_snd _ _
  inverse_target := prod.lift_fst _ _
  associativity := by
    intro T a b d h_ab h_bd h_ab_d h_a_bd
    apply prod.hom_ext
    · simp [pairComposition, prod.lift_fst, pullback.lift_fst_assoc]
    · simp [pairComposition, prod.lift_snd, pullback.lift_snd_assoc]
  right_identity := by
    intro T a h
    apply prod.hom_ext
    · simp [pairComposition, prod.lift_fst, pullback.lift_fst_assoc]
    · simp [pairComposition, prod.lift_snd, pullback.lift_snd_assoc]
  left_identity := by
    intro T a h
    apply prod.hom_ext
    · simp [pairComposition, prod.lift_fst, pullback.lift_fst_assoc]
    · simp [pairComposition, prod.lift_snd, pullback.lift_snd_assoc]
  inverse_comp := by
    intro T a h
    apply prod.hom_ext
    · simp [pairComposition, prod.lift_fst, pullback.lift_fst_assoc]
    · simp [pairComposition, prod.lift_snd, pullback.lift_snd_assoc]
  comp_inverse := by
    intro T a h
    apply prod.hom_ext
    · simp [pairComposition, prod.lift_fst, pullback.lift_fst_assoc]
    · simp [pairComposition, prod.lift_snd, pullback.lift_snd_assoc]

/-- The object scheme of the pair groupoid is `U`. -/
theorem pair_U {S : Scheme.{u}} (U : Over S) : (pair U).U = U := rfl

/-- The arrow scheme of the pair groupoid is `U ⨯ U`. -/
theorem pair_R {S : Scheme.{u}} (U : Over S) : (pair U).R = (U ⨯ U) := rfl

/-- The source map of the pair groupoid is the second projection. -/
theorem pair_s {S : Scheme.{u}} (U : Over S) :
    (pair U).s = (prod.snd : U ⨯ U ⟶ U) := rfl

/-- The target map of the pair groupoid is the first projection. -/
theorem pair_t {S : Scheme.{u}} (U : Over S) :
    (pair U).t = (prod.fst : U ⨯ U ⟶ U) := rfl

/-- Composition in the pair groupoid is the outer-pair map. -/
theorem pair_c {S : Scheme.{u}} (U : Over S) :
    (pair U).c = pairComposition U := rfl

/-- The identity map of the pair groupoid is the diagonal. -/
theorem pair_e {S : Scheme.{u}} (U : Over S) : (pair U).e = diag U := rfl

/-- Inversion in the pair groupoid swaps the two factors. -/
theorem pair_i {S : Scheme.{u}} (U : Over S) :
    (pair U).i = prod.lift (prod.snd : U ⨯ U ⟶ U) prod.fst := rfl

/-- The canonical morphism from a groupoid scheme to the pair groupoid on its objects. -/
noncomputable def toPair {S : Scheme.{u}} (G : GroupoidScheme S) : Hom G (pair G.U) where
  obj := 𝟙 G.U
  arrow := G.toPreRelation.hom
  map_s := by
    change G.s ≫ 𝟙 G.U = prod.lift G.t G.s ≫ prod.snd
    simp [prod.lift_snd]
  map_t := by
    change G.t ≫ 𝟙 G.U = prod.lift G.t G.s ≫ prod.fst
    simp [prod.lift_fst]
  map_c := by
    apply prod.hom_ext
    · simpa [pair, pairComposition, composableMap, pullback.map, toPreRelation,
        Scheme.PreRelation.ofHom, Category.assoc, prod.lift_fst, prod.lift_fst_assoc,
        pullback.lift_fst_assoc] using G.comp_target
    · simpa [pair, pairComposition, composableMap, pullback.map, toPreRelation,
        Scheme.PreRelation.ofHom, Category.assoc, prod.lift_snd, prod.lift_snd_assoc,
        pullback.lift_snd_assoc] using G.comp_source

/-- The object component of the canonical morphism to the pair groupoid is the identity. -/
theorem toPair_obj {S : Scheme.{u}} (G : GroupoidScheme S) :
    (toPair G).obj = 𝟙 G.U := rfl

/-- The arrow component of the canonical morphism to the pair groupoid is `(t, s)`. -/
theorem toPair_arrow {S : Scheme.{u}} (G : GroupoidScheme S) :
    (toPair G).arrow = G.toPreRelation.hom := rfl

/-- The object scheme of `G` agrees with that of its pair groupoid. -/
theorem toPair_object_eq {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.U = (pair G.U).U := rfl

/-- The canonical morphism to the pair groupoid is identity on objects. -/
theorem toPair_isIdentityOnObjects {S : Scheme.{u}} (G : GroupoidScheme S) :
    (toPair G).IsIdentityOnObjects (toPair_object_eq G) := rfl

end AlgebraicGeometry.GroupoidScheme
