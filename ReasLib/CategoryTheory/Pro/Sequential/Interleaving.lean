/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Factorizations and interleavings of sequential inverse systems

A sequential factorization records that the transitions of one inverse system factor coherently
through the stages of another.  An alternating interleaving instead uses a common strictly
increasing reindexing for both systems.  Both presentations produce explicit sequential
representatives in both directions and hence an isomorphism of the associated pro-objects.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v

namespace CategoryTheory.Pro

/-- A coherent factorization of the transitions of `X` through the stages of `Y`.

At stage `i`, the transition from `X(reindex (i + 1))` to `X(reindex i)` factors as
`X(reindex (i + 1)) ⟶ Y(i) ⟶ X(reindex i)`.  The transitions of `Y` are the composites through
the intervening stages of `X`.  The condition `i ≤ reindex i` makes this system of factorizations
cofinal without imposing strictness that is irrelevant to the resulting pro-object. -/
@[stacks 0GZ5 "coherent factorizations of sequential inverse systems"]
structure SequentialFactorization {C : Type u} [Category.{v} C]
    (X Y : SequentialInverseSystem C) where
  /-- The selected stages of `X`. -/
  reindex : ℕ →o ℕ
  /-- Every original stage is dominated by the selected stage with the same index. -/
  le_reindex (i : ℕ) : i ≤ reindex i
  /-- The map from the next selected stage of `X` to the intervening stage of `Y`. -/
  toStage (i : ℕ) :
    X.obj (op (reindex (i + 1))) ⟶ Y.obj (op i)
  /-- The map from an intervening stage of `Y` to the preceding selected stage of `X`. -/
  fromStage (i : ℕ) :
    Y.obj (op i) ⟶ X.obj (op (reindex i))
  /-- The two stage maps recover the selected transition of `X`. -/
  toStage_fromStage (i : ℕ) :
    toStage i ≫ fromStage i =
      X.transitionMap (reindex.monotone (Nat.le_add_right i 1))
  /-- The transition of `Y` is the composite through the corresponding selected stage of `X`. -/
  stepMap (i : ℕ) :
    Y.stepMap i = fromStage (i + 1) ≫ toStage i

namespace SequentialFactorization

variable {C : Type u} [Category.{v} C]
variable {X Y : SequentialInverseSystem C}

/-- The sequential inverse system whose stage `i` is `stage i` and whose step from `i + 1` to `i`
is the composite through `X(reindex (i + 1))`. -/
def ofStagesSystem (X : SequentialInverseSystem C) (reindex : ℕ →o ℕ) (stage : ℕ → C)
    (toStage : ∀ i, X.obj (op (reindex (i + 1))) ⟶ stage i)
    (fromStage : ∀ i, stage i ⟶ X.obj (op (reindex i))) :
    SequentialInverseSystem C :=
  Functor.ofOpSequence (fun i ↦ fromStage (i + 1) ≫ toStage i)

/-- The generating transition of `ofStagesSystem` is its defining composite through `X`. -/
theorem ofStagesSystem_stepMap (X : SequentialInverseSystem C) (reindex : ℕ →o ℕ)
    (stage : ℕ → C) (toStage : ∀ i, X.obj (op (reindex (i + 1))) ⟶ stage i)
    (fromStage : ∀ i, stage i ⟶ X.obj (op (reindex i))) (i : ℕ) :
    (ofStagesSystem X reindex stage toStage fromStage).stepMap i =
      fromStage (i + 1) ≫ toStage i := sorry

/-- Build a coherent sequential factorization directly from stage objects and factorizations of
the selected transitions of `X`.  The intervening inverse system and all of its transitions are
constructed explicitly from the supplied maps. -/
def ofStages (X : SequentialInverseSystem C) (reindex : ℕ →o ℕ)
    (le_reindex : ∀ i, i ≤ reindex i) (stage : ℕ → C)
    (toStage : ∀ i, X.obj (op (reindex (i + 1))) ⟶ stage i)
    (fromStage : ∀ i, stage i ⟶ X.obj (op (reindex i)))
    (factor : ∀ i, toStage i ≫ fromStage i =
      X.transitionMap (reindex.monotone (Nat.le_add_right i 1))) :
    SequentialFactorization X (ofStagesSystem X reindex stage toStage fromStage) where
  reindex := reindex
  le_reindex := le_reindex
  toStage := toStage
  fromStage := fromStage
  toStage_fromStage := factor
  stepMap := ofStagesSystem_stepMap X reindex stage toStage fromStage

/-- The source reindexing of the sequential representative from `X` to `Y`. -/
def homReindex (z : SequentialFactorization X Y) : ℕ →o ℕ where
  toFun i := z.reindex (i + 1)
  monotone' := fun _ _ h ↦ z.reindex.monotone (Nat.add_le_add_right h 1)

/-- The representative from `Y` to `X` uses the identity reindexing. -/
def invReindex (_z : SequentialFactorization X Y) : ℕ →o ℕ :=
  OrderHom.id

/-- The forward representative selects `reindex (i + 1)` at stage `i`. -/
@[simp]
theorem homReindex_apply (z : SequentialFactorization X Y) (i : ℕ) :
    z.homReindex i = z.reindex (i + 1) := sorry

/-- The reverse representative uses stage `i` itself. -/
@[simp]
theorem invReindex_apply (z : SequentialFactorization X Y) (i : ℕ) :
    z.invReindex i = i := sorry

/-- The level map of the representative from `X` to `Y`. -/
def homApp (z : SequentialFactorization X Y) (i : ℕ) :
    X.obj (op (z.homReindex i)) ⟶ Y.obj (op i) :=
  z.toStage i

/-- The level map from `Y(i)` to `X(i)`, obtained by continuing the given factorization map along
the transition from `X(reindex i)` to `X(i)`. -/
def invApp (z : SequentialFactorization X Y) (i : ℕ) :
    Y.obj (op (z.invReindex i)) ⟶ X.obj (op i) :=
  z.fromStage i ≫ X.transitionMap (z.le_reindex i)

/-- The maps from selected stages of `X` commute with adjacent transitions. -/
theorem homApp_naturality (z : SequentialFactorization X Y) (i : ℕ) :
    X.transitionMap
          (z.homReindex.monotone (Nat.le_add_right i 1)) ≫ z.homApp i =
      z.homApp (i + 1) ≫ Y.stepMap i := sorry

/-- The supplied maps from the intervening stages form a natural transformation to the selected
subsystem of `X`. -/
theorem fromStage_naturality (z : SequentialFactorization X Y) (i : ℕ) :
    Y.stepMap i ≫ z.fromStage i =
      z.fromStage (i + 1) ≫
        X.transitionMap (z.reindex.monotone (Nat.le_add_right i 1)) := sorry

/-- The maps from `Y` to the original stages of `X` commute with adjacent transitions. -/
theorem invApp_naturality (z : SequentialFactorization X Y) (i : ℕ) :
    Y.transitionMap
          (z.invReindex.monotone (Nat.le_add_right i 1)) ≫ z.invApp i =
      z.invApp (i + 1) ≫ X.stepMap i := sorry

/-- The natural transformation from the selected subsystem of `X` to `Y`. -/
def homNatTrans (z : SequentialFactorization X Y) :
    z.homReindex.toFunctor.op ⋙ X ⟶ Y :=
  NatTrans.ofOpSequence z.homApp z.homApp_naturality

/-- The natural transformation from `Y` to the subsystem of `X` selected by `reindex`. -/
def fromStageNatTrans (z : SequentialFactorization X Y) :
    Y ⟶ z.reindex.toFunctor.op ⋙ X :=
  NatTrans.ofOpSequence z.fromStage z.fromStage_naturality

/-- The natural transformation from `Y` to the original inverse system `X`. -/
def invNatTrans (z : SequentialFactorization X Y) : Y ⟶ X :=
  NatTrans.ofOpSequence z.invApp z.invApp_naturality

/-- A component of the forward natural transformation is the supplied map to the intervening
stage. -/
@[simp]
theorem homNatTrans_app (z : SequentialFactorization X Y) (i : ℕ) :
    z.homNatTrans.app (op i) = z.toStage i := sorry

/-- A component of the natural transformation to the selected subsystem of `X` is the supplied
map from the intervening stage. -/
@[simp]
theorem fromStageNatTrans_app (z : SequentialFactorization X Y) (i : ℕ) :
    z.fromStageNatTrans.app (op i) = z.fromStage i := sorry

/-- A component of the reverse natural transformation is the supplied map from the intervening
stage followed by the transition to the original index. -/
@[simp]
theorem invNatTrans_app (z : SequentialFactorization X Y) (i : ℕ) :
    z.invNatTrans.app (op i) =
      z.fromStage i ≫ X.transitionMap (z.le_reindex i) := sorry

/-- The sequential pro-morphism representative induced from `X` to `Y`. -/
def hom (z : SequentialFactorization X Y) : SequentialHom X Y where
  reindex := z.homReindex
  hom := z.homNatTrans

/-- The sequential pro-morphism representative induced from `Y` to `X`. -/
def inv (z : SequentialFactorization X Y) : SequentialHom Y X :=
  SequentialHom.ofNatTrans z.invNatTrans

/-- The forward representative has the selected source reindexing. -/
@[simp]
theorem hom_reindex (z : SequentialFactorization X Y) :
    z.hom.reindex = z.homReindex := sorry

/-- A level map of the forward representative is the supplied map to the intervening stage. -/
@[simp]
theorem hom_hom_app (z : SequentialFactorization X Y) (i : ℕ) :
    z.hom.hom.app (op i) = z.toStage i := sorry

/-- The reverse representative has identity source reindexing. -/
@[simp]
theorem inv_reindex (z : SequentialFactorization X Y) :
    z.inv.reindex = OrderHom.id := sorry

/-- A level map of the reverse representative is the supplied map from the intervening stage,
continued to the original index of `X`. -/
@[simp]
theorem inv_hom_app (z : SequentialFactorization X Y) (i : ℕ) :
    z.inv.hom.app (op i) =
      z.fromStage i ≫ X.transitionMap (z.le_reindex i) := sorry

/-- The forward representative followed by the inverse is equivalent to the identity of `X`. -/
theorem hom_inv_equivalent (z : SequentialFactorization X Y) :
    SequentialHom.Equivalent (SequentialHom.comp z.hom z.inv)
      (SequentialHom.id X) := sorry

/-- The inverse representative followed by the forward one is equivalent to the identity of
`Y`. -/
theorem inv_hom_equivalent (z : SequentialFactorization X Y) :
    SequentialHom.Equivalent (SequentialHom.comp z.inv z.hom)
      (SequentialHom.id Y) := sorry

/-- A coherent factorization of transitions gives the forward representative an explicit inverse
up to common refinement. -/
@[stacks 0GZ5 "factorized sequential towers have representative inverses"]
theorem hom_hasRepresentativeInverse (z : SequentialFactorization X Y) :
    z.hom.HasRepresentativeInverse := sorry

/-- A coherent factorization of transitions gives the inverse representative an explicit inverse
up to common refinement. -/
theorem inv_hasRepresentativeInverse (z : SequentialFactorization X Y) :
    z.inv.HasRepresentativeInverse := sorry

/-- Remark 23.12.2 (Tag 0GZ5): coherently factorized sequential inverse systems define isomorphic
pro-objects. -/
@[stacks 0GZ5 "factorized sequential inverse systems are pro-isomorphic"]
theorem hom_isIso (z : SequentialFactorization X Y) :
    IsIso z.hom.toHom := sorry

/-- The reverse representative of a coherent sequential factorization is also an isomorphism of
pro-objects. -/
theorem inv_isIso (z : SequentialFactorization X Y) :
    IsIso z.inv.toHom := sorry

end SequentialFactorization

/-- Lemma 24.35.2 (Stacks 0GZI): alternating level maps along a strictly increasing
reindexing of two sequential inverse systems. -/
@[stacks 0GZI "alternating interleavings of sequential inverse systems"]
structure SequentialInterleaving {C : Type u} [Category.{v} C]
    (X Y : SequentialInverseSystem C) where
  /-- The common strictly increasing reindexing of the two inverse systems. -/
  reindex : ℕ →o ℕ
  /-- The common reindexing is strictly increasing. -/
  strictMono : StrictMono reindex
  /-- The map from the next even stage of `X` to the intervening odd stage of `Y`. -/
  evenToOdd (i : ℕ) :
    X.obj (op (reindex (2 * (i + 1)))) ⟶
      Y.obj (op (reindex (2 * i + 1)))
  /-- The map from an odd stage of `Y` to the preceding even stage of `X`. -/
  oddToEven (i : ℕ) :
    Y.obj (op (reindex (2 * i + 1))) ⟶
      X.obj (op (reindex (2 * i)))
  /-- Two consecutive alternating maps recover the corresponding transition of `X`. -/
  evenComp (i : ℕ) :
    evenToOdd i ≫ oddToEven i =
      X.transitionMap
        (reindex.monotone
          (Nat.mul_le_mul_left 2 (Nat.le_add_right i 1)))
  /-- Two consecutive alternating maps recover the corresponding transition of `Y`. -/
  oddComp (i : ℕ) :
    oddToEven (i + 1) ≫ evenToOdd i =
      Y.transitionMap
        (reindex.monotone
          (Nat.add_le_add_right
            (Nat.mul_le_mul_left 2 (Nat.le_add_right i 1)) 1))

namespace SequentialInterleaving

variable {C : Type u} [Category.{v} C]
variable {X Y : SequentialInverseSystem C}

/-- Transport an interleaving along natural isomorphisms of its two sequential systems. -/
@[stacks 0GZI "transport of sequential interleavings along isomorphisms"]
noncomputable def transport {X' Y' : SequentialInverseSystem C}
    (z : SequentialInterleaving X Y) (eX : X ≅ X') (eY : Y ≅ Y') :
    SequentialInterleaving X' Y' where
  reindex := z.reindex
  strictMono := z.strictMono
  evenToOdd i :=
    eX.inv.app (op (z.reindex (2 * (i + 1)))) ≫ z.evenToOdd i ≫
      eY.hom.app (op (z.reindex (2 * i + 1)))
  oddToEven i :=
    eY.inv.app (op (z.reindex (2 * i + 1))) ≫ z.oddToEven i ≫
      eX.hom.app (op (z.reindex (2 * i)))
  evenComp := sorry
  oddComp := sorry

/-- Transporting an interleaving preserves its reindexing. -/
@[simp]
theorem transport_reindex {X' Y' : SequentialInverseSystem C}
    (z : SequentialInterleaving X Y) (eX : X ≅ X') (eY : Y ≅ Y') :
    (z.transport eX eY).reindex = z.reindex := sorry

/-- The even-to-odd component of a transported interleaving is obtained by conjugating the
original component with the two system isomorphisms. -/
@[simp]
theorem transport_evenToOdd {X' Y' : SequentialInverseSystem C}
    (z : SequentialInterleaving X Y) (eX : X ≅ X') (eY : Y ≅ Y') (i : ℕ) :
    (z.transport eX eY).evenToOdd i =
      eX.inv.app (op (z.reindex (2 * (i + 1)))) ≫ z.evenToOdd i ≫
        eY.hom.app (op (z.reindex (2 * i + 1))) := sorry

/-- The odd-to-even component of a transported interleaving is obtained by conjugating the
original component with the two system isomorphisms. -/
@[simp]
theorem transport_oddToEven {X' Y' : SequentialInverseSystem C}
    (z : SequentialInterleaving X Y) (eX : X ≅ X') (eY : Y ≅ Y') (i : ℕ) :
    (z.transport eX eY).oddToEven i =
      eY.inv.app (op (z.reindex (2 * i + 1))) ≫ z.oddToEven i ≫
        eX.hom.app (op (z.reindex (2 * i))) := sorry

/-- Transport along identity isomorphisms leaves an interleaving unchanged. -/
@[simp]
theorem transport_refl (z : SequentialInterleaving X Y) :
    z.transport (Iso.refl X) (Iso.refl Y) = z := sorry

/-- Successive transports of an interleaving agree with transport along the composite
isomorphisms. -/
theorem transport_trans
    {X' Y' X'' Y'' : SequentialInverseSystem C}
    (z : SequentialInterleaving X Y) (eX : X ≅ X') (eY : Y ≅ Y')
    (eX' : X' ≅ X'') (eY' : Y' ≅ Y'') :
    (z.transport eX eY).transport eX' eY' =
      z.transport (eX.trans eX') (eY.trans eY') := sorry

/-- The source reindexing of the sequential representative from `X` to `Y`. -/
def homReindex (z : SequentialInterleaving X Y) : ℕ →o ℕ where
  toFun n := z.reindex (2 * (n + 1))
  monotone' := fun _ _ h ↦
    z.reindex.monotone
      (Nat.mul_le_mul_left 2 (Nat.add_le_add_right h 1))

/-- The source reindexing of the sequential representative from `Y` to `X`. -/
def invReindex (z : SequentialInterleaving X Y) : ℕ →o ℕ where
  toFun n := z.reindex (2 * n + 1)
  monotone' := fun _ _ h ↦
    z.reindex.monotone
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 1)

/-- Every target index lies below the corresponding reindexed even stage. -/
theorem le_even (z : SequentialInterleaving X Y) (n : ℕ) :
    n ≤ z.reindex (2 * n) := sorry

/-- Every target index lies below the corresponding reindexed odd stage. -/
theorem le_odd (z : SequentialInterleaving X Y) (n : ℕ) :
    n ≤ z.reindex (2 * n + 1) := sorry

/-- The level map of the sequential representative from `X` to `Y`. -/
def homApp (z : SequentialInterleaving X Y) (n : ℕ) :
    X.obj (op (z.homReindex n)) ⟶ Y.obj (op n) :=
  z.evenToOdd n ≫ Y.transitionMap (z.le_odd n)

/-- The level map of the sequential representative from `Y` to `X`. -/
def invApp (z : SequentialInterleaving X Y) (n : ℕ) :
    Y.obj (op (z.invReindex n)) ⟶ X.obj (op n) :=
  z.oddToEven n ≫ X.transitionMap (z.le_even n)

/-- The forward level maps commute with adjacent transitions. -/
theorem homApp_naturality (z : SequentialInterleaving X Y) (n : ℕ) :
    X.transitionMap
          (z.homReindex.monotone (Nat.le_add_right n 1)) ≫ z.homApp n =
      z.homApp (n + 1) ≫ Y.stepMap n := sorry

/-- The inverse level maps commute with adjacent transitions. -/
theorem invApp_naturality (z : SequentialInterleaving X Y) (n : ℕ) :
    Y.transitionMap
          (z.invReindex.monotone (Nat.le_add_right n 1)) ≫ z.invApp n =
      z.invApp (n + 1) ≫ X.stepMap n := sorry

/-- The sequential pro-morphism representative induced from `X` to `Y`. -/
def hom (z : SequentialInterleaving X Y) : SequentialHom X Y where
  reindex := z.homReindex
  hom := NatTrans.ofOpSequence z.homApp z.homApp_naturality

/-- The sequential pro-morphism representative induced from `Y` to `X`. -/
def inv (z : SequentialInterleaving X Y) : SequentialHom Y X where
  reindex := z.invReindex
  hom := NatTrans.ofOpSequence z.invApp z.invApp_naturality

/-- The forward representative followed by the inverse is equivalent to the identity of `X`. -/
theorem hom_inv_equivalent (z : SequentialInterleaving X Y) :
    SequentialHom.Equivalent (SequentialHom.comp z.hom z.inv)
      (SequentialHom.id X) := sorry

/-- The inverse representative followed by the forward one is equivalent to the identity of
`Y`. -/
theorem inv_hom_equivalent (z : SequentialInterleaving X Y) :
    SequentialHom.Equivalent (SequentialHom.comp z.inv z.hom)
      (SequentialHom.id Y) := sorry

/-- Lemma 24.35.2 (Stacks 0GZI): an alternating interleaving gives the forward sequential
representative a representative inverse. -/
@[stacks 0GZI "alternating interleavings induce sequential pro-isomorphisms"]
theorem hom_hasRepresentativeInverse (z : SequentialInterleaving X Y) :
    z.hom.HasRepresentativeInverse := sorry

end SequentialInterleaving

end CategoryTheory.Pro
