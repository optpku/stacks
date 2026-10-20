module

public import stacks_project.Chap96.Lemma_96_14_2_Comparison
public import stacks_project.Chap96.Lemma_96_14_2_Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 96.14.2

If a category fibred in groupoids over `(Sch/S)_fppf` is represented by an
algebraic space `F`, restriction of quasi-coherent modules along 96.10.2.1
is an equivalence `QCoh(𝒪_X) ⥤ QCoh(𝒪_F)` with specified quasi-inverse
`π_F^*`, compatible with pullback along 1-morphisms of such categories.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}}

/-- Lemma 96.14.2 (1): let `S` be a scheme, and let `X → (Sch/S)_fppf` be a
category fibred in groupoids represented by an algebraic space `F` via
`e : F.toGroupoids ≌ X`. The restriction functor 96.10.2.1,
`restrict e : QCoh X ⥤ AlgebraicSpace.QCoh F`, `ℱ ↦ ℱ|_{F_étale}`, is an
equivalence, with specified quasi-inverse `piStar e`, `G ↦ π_F^* G`. -/
@[stacks 0GQD]
def restrictEquivalence {F : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : F.toGroupoids ≌ X) :
    QCoh X ≌ AlgebraicSpace.QCoh F :=
  CategoryTheory.Equivalence.mk (restrict e) (piStar e)
    (piStar_restrictIso e).symm (restrict_piStarIso e).symm

/-- `restrictEquivalence e` is the functor `restrict e`. -/
theorem restrictEquivalence_functor {F : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : F.toGroupoids ≌ X) :
    (restrictEquivalence e).functor = restrict e :=
  rfl

/-- `restrictEquivalence e` has specified inverse `piStar e`. -/
theorem restrictEquivalence_inverse {F : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : F.toGroupoids ≌ X) :
    (restrictEquivalence e).inverse = piStar e :=
  rfl

/-- Restriction of quasi-coherent modules along a representing algebraic space
is an equivalence. -/
instance restrict_isEquivalence {F : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : F.toGroupoids ≌ X) :
    (restrict e).IsEquivalence :=
  (restrictEquivalence e).isEquivalence_functor

variable {X Y : GroupoidsOver S} {F G : AlgebraicSpace S}
variable (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
variable (α : (f ≫ eY.symm.hom) ≅
    (eX.symm.hom ≫ AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f)))

/-- Lemma 96.14.2 (2): the equivalence of (1) is compatible with pullback. For a
1-morphism `f : X ⟶ Y` of categories fibred in groupoids represented by
algebraic spaces via `eX` and `eY`, restriction intertwines `pullback f` with
`AlgebraicSpace.QCoh.pullback (recoveredHom eX eY f)`. -/
@[stacks 0GQD]
def restrict_pullbackIso :
    pullback f ⋙ restrict eX ≅
      restrict eY ⋙ AlgebraicSpace.QCoh.pullback (recoveredHom eX eY f) :=
  restrict_pullbackComparison eX eY f α

/-- `restrict_pullbackIso` is the comparison `restrict_pullbackComparison`. -/
theorem restrict_pullbackIso_eq :
    restrict_pullbackIso eX eY f α =
      restrict_pullbackComparison eX eY f α :=
  rfl

end AlgebraicGeometry.GroupoidsOver.QCoh
