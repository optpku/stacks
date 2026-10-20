module

public import ReasLib.Algebra.PolynomialSite.ChangeOfRings
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CommAlgCat.Over.Polynomial.Site
open scoped CategoryTheory

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (Algebra.PolynomialSite A B)ᵒᵖ AddCommGrpCat.{u + 1}]
variable [Functor.HasLeftDerivedFunctor
    (categoryOverPointColimitToDerived (Algebra.PolynomialSite A B) AddCommGrpCat.{u + 1})
    (HomotopyCategory.quasiIso ((Algebra.PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
      (ComplexShape.up ℤ))]

/- Lemma 92.5.6. For every module F over the polynomial structure sheaf,
Lπ!(F) = Lπ!(Li^* F) = Lπ!(F ⊗_O^L underline{B}) in D(Ab).
Here Li^* and derived tensor denote the same canonical extension of scalars
along the augmentation O → underline{B}. -/
@[stacks 08QJ] #check
  (CommAlgCat.Over.Polynomial.Site.lowerShriek_changeOfRings_obj A B :
    ∀ (F : RingedSite.ModuleCat.{u + 1} (ringedSite A B)),
      IsIsomorphic ((lowerShriek A B).obj (single A B F))
        ((lowerShriekConstant A B).obj ((changeOfRings A B).obj (single A B F))))
