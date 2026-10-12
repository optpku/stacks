/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive

/-!
# Higher Direct Images of Abelian Sheaves

This leaf owns the derived pushforward of sheaves of abelian groups along a
continuous functor of sites.  Ringed-site and topological-space specializations
should build on this site-level owner.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable (u : D ⥤ C) [Functor.IsContinuous u JD JC]
variable [HasSheafify JC AddCommGrpCat.{v}] [HasSheafify JD AddCommGrpCat.{v}]
variable [HasInjectiveResolutions (Sheaf JC AddCommGrpCat.{v})]

/-- The degree-`i` higher direct image functor on abelian sheaves along a continuous functor of
sites. -/
abbrev higherDirectImageFunctor (i : ℕ) :
    Sheaf JC AddCommGrpCat.{v} ⥤ Sheaf JD AddCommGrpCat.{v} :=
  (u.sheafPushforwardContinuous AddCommGrpCat.{v} JD JC).rightDerived i

/-- The degree-`i` higher direct image of an abelian sheaf along a continuous functor of sites. -/
abbrev higherDirectImage (F : Sheaf JC AddCommGrpCat.{v}) (i : ℕ) :
    Sheaf JD AddCommGrpCat.{v} :=
  (higherDirectImageFunctor u i).obj F

/-- The map induced on higher direct images by a morphism of abelian sheaves. -/
abbrev higherDirectImageMap {F G : Sheaf JC AddCommGrpCat.{v}} (f : F ⟶ G) (i : ℕ) :
    @higherDirectImage C _ D _ JC JD u _ _ _ _ F i ⟶
      @higherDirectImage C _ D _ JC JD u _ _ _ _ G i :=
  (higherDirectImageFunctor u i).map f

/- Lean surface notation for the higher direct image `R⁽i⁾[u](F)`. A thin macro keeps instance
search at use sites instead of forcing it during notation elaboration. -/
scoped macro:max "R⁽" i:term "⁾[" u:term "](" F:term ")" : term =>
  `(@higherDirectImage _ _ _ _ _ _ $u _ _ _ _ $F $i)

namespace HigherDirectImage

/-- A chosen injective resolution computes a higher direct image by applying the sheaf pushforward
degreewise and taking homology. -/
@[stacks 071F "higher direct image from an injective resolution"]
noncomputable abbrev isoHomologyPushforward
    (F : Sheaf JC AddCommGrpCat.{v}) (I : InjectiveResolution F) (i : ℕ) :
    higherDirectImage u F i ≅
      (HomologicalComplex.homologyFunctor (Sheaf JD AddCommGrpCat.{v})
        (ComplexShape.up ℕ) i).obj
          (((u.sheafPushforwardContinuous AddCommGrpCat.{v} JD JC).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex) :=
  I.isoRightDerivedObj (u.sheafPushforwardContinuous AddCommGrpCat.{v} JD JC) i

end HigherDirectImage

end

end CategoryTheory.Sheaf
