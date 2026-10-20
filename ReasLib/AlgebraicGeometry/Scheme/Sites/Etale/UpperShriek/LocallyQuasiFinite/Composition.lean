module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.GeneralComposition

/-!
# Composition of locally quasi-finite étale upper shriek

The canonical composition isomorphism for non-derived upper shriek on abelian
étale sheaves is obtained by uniqueness of right adjoints from composition of
compact-support direct images. These identifications satisfy associativity.
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
def lowerShriekCompAdjunction [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    lowerShriek f ⋙ lowerShriek g ⊣ upperShriek g ⋙ upperShriek f :=
  (lowerShriekAdjunction f).comp (lowerShriekAdjunction g)

variable [LocallyOfFiniteType f] [LocallyOfFiniteType g]
variable [HasCoproducts.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- The canonical composition isomorphism `(g ∘ f)^! ≅ f^! ∘ g^!` on abelian
étale sheaves for locally quasi-finite, locally finite-type morphisms. -/
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

/-- The composition isomorphism is the right-adjoint uniqueness isomorphism
obtained by transporting the composed compact-support adjunction. -/
theorem upperShriekCompIso_eq :
    upperShriekCompIso f g =
      (lowerShriekAdjunction (f ≫ g)).rightAdjointUniq
        ((lowerShriekCompAdjunction f g).ofNatIsoLeft
          (lowerShriekFunctorCompIso f g).symm) :=
  rfl

section assoc

variable {T : Scheme.{u}} (h : Z ⟶ T)
variable [LocallyQuasiFinite h] [LocallyOfFiniteType h]
variable [HasCoproducts.{u} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]

/-- Upper shriek is unchanged by reassociation of a triple composite. -/
theorem upperShriek_assoc :
    upperShriek ((f ≫ g) ≫ h) = upperShriek (f ≫ g ≫ h) :=
  sorry

/-- The canonical upper-shriek composition identifications satisfy the
associativity square for three locally quasi-finite, locally finite-type morphisms. -/
theorem upperShriekCompIso_assoc :
    (upperShriekCompIso (f ≫ g) h).hom ≫
        whiskerLeft (upperShriek h) (upperShriekCompIso f g).hom =
      eqToHom (upperShriek_assoc f g h) ≫
        (upperShriekCompIso f (g ≫ h)).hom ≫
        whiskerRight (upperShriekCompIso g h).hom (upperShriek f) ≫
        (associator (upperShriek h) (upperShriek g) (upperShriek f)).hom :=
  sorry

end assoc

end AlgebraicGeometry.Scheme.Etale

end
