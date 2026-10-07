module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Diagonal, flip, and transitivity pairings of a pre-relation

The diagonal, flip, and transitivity pairings of a pre-relation on an algebraic space over a base
are morphisms into the binary product in the slice category.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- The diagonal pairing of an algebraic space over a base, sending `u` to `(u, u)`. -/
def diagonalPairing {S : Scheme.{u}} {B : AlgebraicSpace S} (U : Over B) :
    U ⟶ U ⨯ U :=
  diag U

/-- The flip of a pre-relation, sending `r` to `(s(r), t(r))`. -/
def flipHom {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) :
    P.left ⟶ U ⨯ U :=
  prod.lift P.s P.t

/-- The first projection of `P.flipHom` is the source map. -/
theorem flipHom_fst {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    P.flipHom ≫ prod.fst = P.s := sorry

/-- The second projection of `P.flipHom` is the target map. -/
theorem flipHom_snd {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    P.flipHom ≫ prod.snd = P.t := sorry

/-- The flip is the defining map of `P` composed with the braiding of `U ⨯ U`. -/
theorem flipHom_eq_braiding {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    P.flipHom = P.hom ≫ (prod.braiding U U).hom := sorry

/-- The transitivity pairing of a pre-relation, sending `(r, r')` to `(t(r), s(r'))`. -/
def compPair {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U) :
    pullback P.s P.t ⟶ U ⨯ U :=
  prod.lift (pullback.fst P.s P.t ≫ P.t) (pullback.snd P.s P.t ≫ P.s)

/-- The first projection of `P.compPair` is the target of the first composable arrow. -/
theorem compPair_fst {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    P.compPair ≫ prod.fst = pullback.fst P.s P.t ≫ P.t := sorry

/-- The second projection of `P.compPair` is the source of the second composable arrow. -/
theorem compPair_snd {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    P.compPair ≫ prod.snd = pullback.snd P.s P.t ≫ P.s := sorry

/-- The transitivity pairing is characterized by its two projections. -/
theorem compPair_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    P.compPair ≫ prod.fst = pullback.fst P.s P.t ≫ P.t ∧
      P.compPair ≫ prod.snd = pullback.snd P.s P.t ≫ P.s := sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
