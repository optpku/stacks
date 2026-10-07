module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Resize
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»
public import stacks_project.Chap99.«99_15_1_1_Curves»

/-!
# Base-change pair category of families of curves

For an algebraic space `B` over a scheme `S`, the pair category `B-Curves` is the
costructured-arrow category of `pCurvesGroupoids S ⋙ ofOverFunctor S` into `B`. It is the
apex of a 2-fibre product square over `Curves → Sch` along `(Sch/B) → Sch`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- The category of pairs `(P : CurvesGroupoids S, h : ofOver (p.obj P) ⟶ B)`, written
`B-Curves` in the source. Morphisms are morphisms of `CurvesGroupoids S` commuting
with the maps to `B`. Here `Over S` plays the role of `Sch_fppf` and `SchemeOver B`
plays the role of `(Sch/B)_fppf`. -/
abbrev CurvesGroupoidsOver {S : Scheme.{u}} (B : AlgebraicSpace S) :=
  CostructuredArrow (pCurvesGroupoids S ⋙ ofOverFunctor S) B

namespace CurvesGroupoidsOver

/-- Package a family of curves `P` with a morphism from its base scheme into `B`. -/
def mk {S : Scheme.{u}} {B : AlgebraicSpace S} (P : CurvesGroupoids S)
    (h : (ofOverFunctor S).obj ((pCurvesGroupoids S).obj P) ⟶ B) :
    CurvesGroupoidsOver B :=
  CostructuredArrow.mk h

/-- The underlying object of `mk P h` is `P`. -/
theorem mk_left {S : Scheme.{u}} {B : AlgebraicSpace S} (P : CurvesGroupoids S)
    (h : (ofOverFunctor S).obj ((pCurvesGroupoids S).obj P) ⟶ B) :
    (mk P h).left = P :=
  sorry

/-- The structural morphism of `mk P h` is `h`. -/
theorem mk_hom {S : Scheme.{u}} {B : AlgebraicSpace S} (P : CurvesGroupoids S)
    (h : (ofOverFunctor S).obj ((pCurvesGroupoids S).obj P) ⟶ B) :
    (mk P h).hom = h :=
  sorry

/-- A morphism `(P, h) ⟶ (Q, h')` in `CurvesGroupoidsOver B` is a morphism `φ` of
`CurvesGroupoids` such that `h ∘ g = h'`. -/
theorem hom_w {S : Scheme.{u}} {B : AlgebraicSpace S} {P Q : CurvesGroupoidsOver B}
    (φ : P ⟶ Q) :
    (pCurvesGroupoids S ⋙ ofOverFunctor S).map φ.left ≫ Q.hom = P.hom :=
  sorry

/-- The commutative square with apex `CurvesGroupoidsOver B`, projecting to
`CurvesGroupoids S` and to `SchemeOver B`. -/
def square {S : Scheme.{u}} (B : AlgebraicSpace S) :
    CatCommSqOver (pCurvesGroupoids S) (CostructuredArrow.proj (ofOverFunctor S) B)
      (CurvesGroupoidsOver B) where
  fst := CostructuredArrow.proj (pCurvesGroupoids S ⋙ ofOverFunctor S) B
  snd := CostructuredArrow.pre (pCurvesGroupoids S) (ofOverFunctor S) B
  iso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} _ ↦ rfl)

/-- The comparison from `CurvesGroupoidsOver B` to the explicit categorical pullback of
`pCurvesGroupoids S` and `SchemeOver B ⥤ Over S`. -/
abbrev comparison {S : Scheme.{u}} (B : AlgebraicSpace S) :=
  (square B).comparison

/-- The comparison functor is an equivalence when the square is a 2-fibre product. -/
instance comparison_isEquivalence {S : Scheme.{u}} (B : AlgebraicSpace S)
    [CatCommSqOver.Resized.IsBilimit (square B)] :
    (comparison B).IsEquivalence :=
  sorry

end CurvesGroupoidsOver

end AlgebraicGeometry.AlgebraicSpace.Spaces
