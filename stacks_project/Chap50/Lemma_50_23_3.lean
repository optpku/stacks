/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.ClosedImmersion
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory Opposite Scheme.Hom
open scoped AlgebraicGeometry

universe u

#check (@AlgebraicGeometry.Scheme.DeRham.Gysin.mapOfClosedImmersion :
  {Z X S : Scheme.{u}} → (i : Z ⟶ X) → [IsClosedImmersion i] →
    [Scheme.Hom.FinitePresentation i] → (f : X ⟶ S) → (c p : ℕ) →
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] →
      (Scheme.Modules.toRingedSpace X).obj
          ((Scheme.Modules.pushforward i).obj
            (SheafOfModules.RingedSite.ExteriorPower.sheaf
              Z.𝒪 Ω[(i ≫ f).toShHom] p)) ⟶
        (Scheme.Hom.LocalCohomology.functor i c).obj
          (AlgebraicGeometry.Scheme.DeRham.Gysin.relativeFormQCoh f (p + c)))

/- Lemma 50.23.3: the canonical Gysin morphism for a finitely presented closed immersion
with rank-`c` locally free conormal sheaf agrees locally with the morphism determined by any
ordered equation presentation. -/
@[stacks 0G86] #check
  (@AlgebraicGeometry.Scheme.DeRham.Gysin.mapOfClosedImmersion_ofPresentation :
    {Z X S : Scheme.{u}} → (i : Z ⟶ X) → [IsClosedImmersion i] →
      [Scheme.Hom.FinitePresentation i] → (f : X ⟶ S) → (c p : ℕ) →
      [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] →
      (P : Scheme.Hom.LocalCohomology.EquationPresentation i c) →
        (CategoryTheory.forget₂ _ _).map
              (((Scheme.Modules.pushforward i).map
                (AlgebraicGeometry.Scheme.DeRham.Gysin.pullbackFormToClosedForm i f p)).val.app
                  (op P.carrier)) ≫
            (CategoryTheory.forget₂ _ _).map
              ((AlgebraicGeometry.Scheme.DeRham.Gysin.mapOfClosedImmersion i f c p).val.app
                (op P.carrier)) =
          AlgebraicGeometry.Scheme.DeRham.Gysin.equationGysinSourceComparison i f c p P ≫
            (CategoryTheory.forget₂ _ _).map
              ((AlgebraicGeometry.Scheme.DeRham.Gysin.map
                (P.carrier.ι ≫ f) P.generators p).val.app (op ⊤)) ≫
            AlgebraicGeometry.Scheme.DeRham.Gysin.equationGysinTargetComparison
              i f c (p + c) P)
