/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Remark_76_17_7_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

noncomputable section

universe u

/- Remark 76.17.7 (1): if `B` is a thickening `Z ⊂ Z' = B` and
`Y = Z ×_{Z'} Y'`, then `A : a^* C_{Y/Y'} ⟶ C_{X/X'}` is uniquely determined
by `a`. -/
@[stacks 0CK7] #check
  (determinedConormal_unique :
    ∀ {S : Scheme.{u}} {Z Z' X X' Y Y' : AlgebraicSpace S}
      (iZ : Z ⟶ Z') (iX : X ⟶ X') (iY : Y ⟶ Y')
      (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
      [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
      (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
      (A A' : (Modules.pullback a).obj (Hom.conormalSheaf iY) ⟶ Hom.conormalSheaf iX),
      IsDeterminedConormal iZ iX iY h h' g' a sqY sqX A →
        IsDeterminedConormal iZ iX iY h h' g' a sqY sqX A' → A = A')

/- Remark 76.17.7 (2): in this special case the sheaf of Lemma 76.17.4 is the
rule sending `U'` to morphisms `a' : U' ⟶ Y'` over `Z'` with `a'|_U = a|_U`. -/
@[stacks 0CK7] #check
  (sections_eq_restrictedSections :
    ∀ {S : Scheme.{u}} {Z Z' X X' Y Y' : AlgebraicSpace S}
      (iZ : Z ⟶ Z') (iX : X ⟶ X') (iY : Y ⟶ Y')
      (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
      [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
      (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
      (A : (Modules.pullback a).obj (Hom.conormalSheaf iY) ⟶ Hom.conormalSheaf iX),
      IsDeterminedConormal iZ iX iY h h' g' a sqY sqX A →
        ∀ (U' : spacesEtaleSite X'),
          sections g' h' iX iY a A U' = restrictedSections g' h' iX iY a U')

/- Remark 76.17.7 (3): the sheaf `Hom_𝒪_X(a^* Ω_{Y/Z}, C_{X/X'})` acts on this
sheaf of restricted lifts. -/
@[stacks 0CK7] #check
  (existsUnique_restrictedPerturbation :
    ∀ {S : Scheme.{u}} {Z Z' X X' Y Y' : AlgebraicSpace S}
      (iZ : Z ⟶ Z') (iX : X ⟶ X') (iY : Y ⟶ Y')
      (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
      [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
      (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
      (U' : spacesEtaleSite X') (θ : closedParameterHom iX h a U')
      (s : U'.left ⟶ Y'),
      s ∈ restrictedSections g' h' iX iY a U' →
        ExistsUnique fun t : U'.left ⟶ Y' ↦
          IsRestrictedPerturbation g' h' iX iY h a U' θ s t)
