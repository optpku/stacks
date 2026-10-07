module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.Pullback
public import stacks_project.Chap59.Lemma_59_54_1
public import stacks_project.Chap63.Lemma_63_4_10
public import stacks_project.Chap63.Lemma_63_6_1_UpperShriek

/-!
# Base change for locally quasi-finite étale upper shriek

Lemma 63.6.5: in a cartesian square of schemes with `f` locally quasi-finite,
upper shriek commutes with étale pushforward on abelian sheaves, by uniqueness
of adjoints from the dual lower-shriek base change.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The composed adjunction `f_! ⋙ g⁻¹ ⊣ g_* ⋙ f^!` on abelian étale sheaves. -/
def lowerShriekPullbackAdjunction {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyQuasiFinite f] :
    lowerShriek f ⋙ etaleAbelianSheafPullback g ⊣
      etaleAbelianPushforward g ⋙ upperShriek f :=
  (lowerShriekAdjunction f).comp
    ((smallEtalePullback g).sheafAdjunctionContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology Y'.smallEtaleTopology)

/-- The composed adjunction `(g')⁻¹ ⋙ (f')_! ⊣ (f')^! ⋙ (g')_*` on abelian étale
sheaves. -/
def pullbackLowerShriekAdjunction {X X' Y' : Scheme.{u}} (f' : X' ⟶ Y')
    (g' : X' ⟶ X) [LocallyQuasiFinite f'] :
    etaleAbelianSheafPullback g' ⋙ lowerShriek f' ⊣
      upperShriek f' ⋙ etaleAbelianPushforward g' :=
  ((smallEtalePullback g').sheafAdjunctionContinuous AddCommGrpCat.{u}
      X.smallEtaleTopology X'.smallEtaleTopology).comp
    (lowerShriekAdjunction f')

section

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']

/-- Lemma 63.6.5: Consider a cartesian square of schemes with `f` locally
quasi-finite. For any abelian sheaf `F` in `Ab(Y'_étale)` there is a canonical
identification `(g')_* ((f')^! F) ≅ f^! (g_* F)`. -/
@[stacks 0F6U]
def upperShriekBaseChangeIso :
    upperShriek f' ⋙ etaleAbelianPushforward g' ≅
      etaleAbelianPushforward g ⋙ upperShriek f :=
  (pullbackLowerShriekAdjunction f' g').rightAdjointUniq
    ((lowerShriekPullbackAdjunction f g).ofNatIsoLeft
      (lowerShriekBaseChangeIso f g f' g' h_cart))

/-- The objectwise identification `(g')_* ((f')^! F) ≅ f^! (g_* F)` at an abelian
étale sheaf `F`. -/
def upperShriekBaseChangeIso_app
    (F : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianPushforward g').obj ((upperShriek f').obj F) ≅
      (upperShriek f).obj ((etaleAbelianPushforward g).obj F) :=
  (upperShriekBaseChangeIso f g f' g' h_cart).app F

/-- `upperShriekBaseChangeIso` is the uniqueness isomorphism of the transported
composed adjunctions. -/
theorem upperShriekBaseChangeIso_eq :
    upperShriekBaseChangeIso f g f' g' h_cart =
      (pullbackLowerShriekAdjunction f' g').rightAdjointUniq
        ((lowerShriekPullbackAdjunction f g).ofNatIsoLeft
          (lowerShriekBaseChangeIso f g f' g' h_cart)) :=
  sorry

end

section

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]

/-- Specialization of the upper-shriek base-change identification to the chosen
pullback square of `g` and `f`. -/
def upperShriekBaseChangeIso_pullback :
    upperShriek (pullback.fst g f) ⋙ etaleAbelianPushforward (pullback.snd g f) ≅
      etaleAbelianPushforward g ⋙ upperShriek f :=
  upperShriekBaseChangeIso f g (pullback.fst g f) (pullback.snd g f)
    (IsPullback.of_hasPullback g f).flip

end

end AlgebraicGeometry.Scheme.Etale

end
