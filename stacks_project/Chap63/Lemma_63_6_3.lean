/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import stacks_project.Chap63.Lemma_63_4_12
public import stacks_project.Chap63.Lemma_63_6_1_UpperShriek

/-!
# Composition of locally quasi-finite étale upper shriek

For composable locally quasi-finite scheme morphisms `f : X ⟶ Y` and
`g : Y ⟶ Z` there is a canonical functor isomorphism
`(g ∘ f)^! ≅ f^! ∘ g^!` on abelian étale sheaves, obtained by uniqueness
of right adjoints from `(g ∘ f)_! ≅ g_! ∘ f_!`. A third locally
quasi-finite morphism yields an associativity square of these
identifications.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [LocallyQuasiFinite f] [LocallyQuasiFinite g]

/-- The composed adjunction `f_! ⋙ g_! ⊣ g^! ⋙ f^!` on abelian étale sheaves. -/
def lowerShriekCompAdjunction :
    lowerShriek f ⋙ lowerShriek g ⊣ upperShriek g ⋙ upperShriek f :=
  (lowerShriekAdjunction f).comp (lowerShriekAdjunction g)

variable [LocallyOfFiniteType f] [LocallyOfFiniteType g]
variable [HasCoproducts.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- Lemma 63.6.3 (1): Let `f : X ⟶ Y` and `g : Y ⟶ Z` be separated and locally
quasi-finite morphisms. There is a canonical isomorphism
`(g ∘ f)^! ⟶ f^! ∘ g^!`, i.e.
`upperShriek (f ≫ g) ≅ upperShriek g ⋙ upperShriek f`. -/
@[stacks 0F5B]
def upperShriekCompIso :
    upperShriek (f ≫ g) ≅ upperShriek g ⋙ upperShriek f :=
  (lowerShriekAdjunction (f ≫ g)).rightAdjointUniq
    ((lowerShriekCompAdjunction f g).ofNatIsoLeft
      (lowerShriekFunctorCompIso f g).symm)

/-- The objectwise identification `(f ≫ g)^! G ≅ f^! (g^! G)` at an abelian
étale sheaf `G`. -/
def upperShriekCompIso_app
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) :
    (upperShriek (f ≫ g)).obj G ≅
      (upperShriek f).obj ((upperShriek g).obj G) :=
  (upperShriekCompIso f g).app G

/-- `upperShriekCompIso` is the uniqueness isomorphism of the transported
composed adjunctions. -/
theorem upperShriekCompIso_eq :
    upperShriekCompIso f g =
      (lowerShriekAdjunction (f ≫ g)).rightAdjointUniq
        ((lowerShriekCompAdjunction f g).ofNatIsoLeft
          (lowerShriekFunctorCompIso f g).symm) :=
  sorry

section assoc

variable {T : Scheme.{u}} (h : Z ⟶ T)
variable [LocallyQuasiFinite h] [LocallyOfFiniteType h]
variable [HasCoproducts.{u} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]

/-- `upperShriek` depends only on the underlying morphism, so it is unchanged
by reassociation of a triple composite. -/
theorem upperShriek_assoc :
    upperShriek ((f ≫ g) ≫ h) = upperShriek (f ≫ g ≫ h) :=
  sorry

/-- Left-then-bottom path of the associativity square. -/
def upperShriekCompIso_assoc_left :
    upperShriek ((f ≫ g) ≫ h) ⟶
      upperShriek h ⋙ upperShriek g ⋙ upperShriek f :=
  (upperShriekCompIso (f ≫ g) h).hom ≫
    whiskerLeft (upperShriek h) (upperShriekCompIso f g).hom

/-- Top-then-right path of the associativity square. -/
def upperShriekCompIso_assoc_right :
    upperShriek (f ≫ g ≫ h) ⟶
      upperShriek h ⋙ upperShriek g ⋙ upperShriek f :=
  (upperShriekCompIso f (g ≫ h)).hom ≫
    whiskerRight (upperShriekCompIso g h).hom (upperShriek f) ≫
    (associator (upperShriek h) (upperShriek g) (upperShriek f)).hom

/-- Lemma 63.6.3 (2): Given a third locally quasi-finite morphism `h : Z ⟶ T`
the associativity diagram of composition identifications commutes. -/
@[stacks 0F5B]
theorem upperShriekCompIso_assoc :
    upperShriekCompIso_assoc_left f g h =
      eqToHom (upperShriek_assoc f g h) ≫
        upperShriekCompIso_assoc_right f g h :=
  sorry

end assoc

end AlgebraicGeometry.Scheme.Etale

end
