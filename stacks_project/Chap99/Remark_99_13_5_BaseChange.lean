/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Resize
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»
public import stacks_project.Chap99.Lemma_99_13_1_Spaces

/-!
# Base-change pair categories of primed algebraic spaces

For an algebraic space `B` over a scheme `S`, the pair category `B-Spaces'_ft` is the
costructured-arrow category of `pFtGroupoids S ⋙ ofOverFunctor S` into `B`. It is the
apex of a 2-fibre product square over `Spaces'_ft → Sch` along `(Sch/B) → Sch`. The same
construction applies to `B-Spaces'_{fp, flat, proper}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- The category of pairs `(P : FtGroupoids S, h : ofOver (p.obj P) ⟶ B)`, written
`B-Spaces'_ft` in the source. Morphisms are morphisms of `FtGroupoids S` commuting
with the maps to `B`. Here `Over S` plays the role of `Sch_fppf` and `SchemeOver B`
plays the role of `(Sch/B)_fppf`. -/
abbrev FtGroupoidsOver {S : Scheme.{u}} (B : AlgebraicSpace S) :=
  CostructuredArrow (pFtGroupoids S ⋙ ofOverFunctor S) B

namespace FtGroupoidsOver

/-- Package a finite-type primed space `P` with a morphism from its base scheme into `B`. -/
def mk {S : Scheme.{u}} {B : AlgebraicSpace S} (P : FtGroupoids S)
    (h : (ofOverFunctor S).obj ((pFtGroupoids S).obj P) ⟶ B) :
    FtGroupoidsOver B :=
  CostructuredArrow.mk h

/-- The underlying object of `mk P h` is `P`. -/
theorem mk_left {S : Scheme.{u}} {B : AlgebraicSpace S} (P : FtGroupoids S)
    (h : (ofOverFunctor S).obj ((pFtGroupoids S).obj P) ⟶ B) :
    (mk P h).left = P :=
  sorry

/-- The structural morphism of `mk P h` is `h`. -/
theorem mk_hom {S : Scheme.{u}} {B : AlgebraicSpace S} (P : FtGroupoids S)
    (h : (ofOverFunctor S).obj ((pFtGroupoids S).obj P) ⟶ B) :
    (mk P h).hom = h :=
  sorry

/-- A morphism `(P, h) ⟶ (Q, h')` in `FtGroupoidsOver B` is a morphism `φ` of
`FtGroupoids` such that `h ∘ g = h'`. -/
theorem hom_w {S : Scheme.{u}} {B : AlgebraicSpace S} {P Q : FtGroupoidsOver B}
    (φ : P ⟶ Q) :
    (pFtGroupoids S ⋙ ofOverFunctor S).map φ.left ≫ Q.hom = P.hom :=
  sorry

/-- The commutative square with apex `FtGroupoidsOver B`, projecting to
`FtGroupoids S` and to `SchemeOver B`. -/
def square {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CatCommSqOver (pFtGroupoids S) (CostructuredArrow.proj (ofOverFunctor S) B)
      (FtGroupoidsOver B) where
  fst := CostructuredArrow.proj (pFtGroupoids S ⋙ ofOverFunctor S) B
  snd := CostructuredArrow.pre (pFtGroupoids S) (ofOverFunctor S) B
  iso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} _ ↦ rfl)

/-- The comparison from `FtGroupoidsOver B` to the explicit categorical pullback of
`pFtGroupoids S` and `SchemeOver B ⥤ Over S`. -/
abbrev comparison {S : Scheme.{u}} (B : AlgebraicSpace S) :=
  (square B).comparison

/-- The comparison functor is an equivalence when the square is a 2-fibre product. -/
instance comparison_isEquivalence {S : Scheme.{u}} (B : AlgebraicSpace S)
    [CatCommSqOver.Resized.IsBilimit (square B)] :
    (comparison B).IsEquivalence :=
  sorry

end FtGroupoidsOver

/-- The category of pairs `(P : FpFlatProperGroupoids S, h : ofOver (p.obj P) ⟶ B)`,
written `B-Spaces'_{fp, flat, proper}` in the source. -/
abbrev FpFlatProperGroupoidsOver {S : Scheme.{u}} (B : AlgebraicSpace S) :=
  CostructuredArrow (pFpFlatProperGroupoids S ⋙ ofOverFunctor S) B

namespace FpFlatProperGroupoidsOver

/-- Package an fp-flat-proper primed space `P` with a morphism from its base scheme into `B`. -/
def mk {S : Scheme.{u}} {B : AlgebraicSpace S} (P : FpFlatProperGroupoids S)
    (h : (ofOverFunctor S).obj ((pFpFlatProperGroupoids S).obj P) ⟶ B) :
    FpFlatProperGroupoidsOver B :=
  CostructuredArrow.mk h

/-- The underlying object of `mk P h` is `P`. -/
theorem mk_left {S : Scheme.{u}} {B : AlgebraicSpace S} (P : FpFlatProperGroupoids S)
    (h : (ofOverFunctor S).obj ((pFpFlatProperGroupoids S).obj P) ⟶ B) :
    (mk P h).left = P :=
  sorry

/-- The structural morphism of `mk P h` is `h`. -/
theorem mk_hom {S : Scheme.{u}} {B : AlgebraicSpace S} (P : FpFlatProperGroupoids S)
    (h : (ofOverFunctor S).obj ((pFpFlatProperGroupoids S).obj P) ⟶ B) :
    (mk P h).hom = h :=
  sorry

/-- A morphism `(P, h) ⟶ (Q, h')` in `FpFlatProperGroupoidsOver B` is a morphism of
`FpFlatProperGroupoids` such that `h ∘ g = h'`. -/
theorem hom_w {S : Scheme.{u}} {B : AlgebraicSpace S}
    {P Q : FpFlatProperGroupoidsOver B} (φ : P ⟶ Q) :
    (pFpFlatProperGroupoids S ⋙ ofOverFunctor S).map φ.left ≫ Q.hom = P.hom :=
  sorry

/-- The commutative square with apex `FpFlatProperGroupoidsOver B`, projecting to
`FpFlatProperGroupoids S` and to `SchemeOver B`. -/
def square {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CatCommSqOver (pFpFlatProperGroupoids S)
      (CostructuredArrow.proj (ofOverFunctor S) B) (FpFlatProperGroupoidsOver B) where
  fst := CostructuredArrow.proj (pFpFlatProperGroupoids S ⋙ ofOverFunctor S) B
  snd := CostructuredArrow.pre (pFpFlatProperGroupoids S) (ofOverFunctor S) B
  iso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} _ ↦ rfl)

/-- The comparison from `FpFlatProperGroupoidsOver B` to the explicit categorical
pullback of `pFpFlatProperGroupoids S` and `SchemeOver B ⥤ Over S`. -/
abbrev comparison {S : Scheme.{u}} (B : AlgebraicSpace S) :=
  (square B).comparison

/-- The comparison functor is an equivalence when the square is a 2-fibre product. -/
instance comparison_isEquivalence {S : Scheme.{u}} (B : AlgebraicSpace S)
    [CatCommSqOver.Resized.IsBilimit (square B)] :
    (comparison B).IsEquivalence :=
  sorry

end FpFlatProperGroupoidsOver

end AlgebraicGeometry.AlgebraicSpace.Spaces
