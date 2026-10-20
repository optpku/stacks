/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.PullbackThickening
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

noncomputable section

universe u

/- Remark 76.17.7 (1): if `B` is a thickening `Z ⊂ Z' = B` and
`Y = Z ×_{Z'} Y'`, then `A : a^* C_{Y/Y'} ⟶ C_{X/X'}` is uniquely determined
by `a`. -/
@[stacks 0CK7] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.determinedConormal_unique :
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
  (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.sections_eq_restrictedSections :
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
  (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.existsUnique_restrictedPerturbation :
    ∀ {S : Scheme.{u}} {Z Z' X X' Y Y' : AlgebraicSpace S}
      (iZ : Z ⟶ Z') (iX : X ⟶ X') (iY : Y ⟶ Y')
      (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
      [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
      (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
      (U' : spacesEtaleSite X') (θ : parameterHom h iX (𝟙 Y) a U')
      (s : U'.left ⟶ Y'),
      s ∈ restrictedSections g' h' iX iY a U' →
        ExistsUnique fun t : U'.left ⟶ Y' ↦
          IsRestrictedPerturbation g' h' iX iY h a U' θ s t)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.restrictedSectionsSheaf :
    ∀ {S : Scheme.{u}} {Z' X X' Y Y' : AlgebraicSpace S}
      (g' : X' ⟶ Z') (h' : Y' ⟶ Z')
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY],
    Sheaf (spacesEtaleTopology X') (Type (u + 1)))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.restrictedSectionsSheaf_obj :
    ∀ {S : Scheme.{u}} {Z' X X' Y Y' : AlgebraicSpace S}
      (g' : X' ⟶ Z') (h' : Y' ⟶ Z')
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (U' : spacesEtaleSite X'),
    (restrictedSectionsSheaf g' h' iX iY a).obj.obj (op U') =
      { a' : U'.left ⟶ Y' // a' ∈ restrictedSections g' h' iX iY a U' })

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.restricted_act_simplyTransitive :
    ∀ {S : Scheme.{u}} {Z Z' X X' Y Y' : AlgebraicSpace S}
      (iZ : Z ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    (U' : spacesEtaleSite X') (s t : U'.left ⟶ Y')
    (hs : s ∈ restrictedSections g' h' iX iY a U')
    (ht : t ∈ restrictedSections g' h' iX iY a U'),
    ExistsUnique fun θ : parameterHom h iX (𝟙 Y) a U' ↦
      IsRestrictedPerturbation g' h' iX iY h a U' θ s t)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.restricted_act_zero :
    ∀ {S : Scheme.{u}} {Z Z' X X' Y Y' : AlgebraicSpace S}
      (iZ : Z ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    (U' : spacesEtaleSite X') (s : U'.left ⟶ Y')
    (hs : s ∈ restrictedSections g' h' iX iY a U'),
    IsRestrictedPerturbation g' h' iX iY h a U' 0 s s)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.restricted_act_add :
    ∀ {S : Scheme.{u}} {Z Z' X X' Y Y' : AlgebraicSpace S}
      (iZ : Z ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    (U' : spacesEtaleSite X') (θ η : parameterHom h iX (𝟙 Y) a U')
    (s t : U'.left ⟶ Y'),
    IsRestrictedPerturbation g' h' iX iY h a U' (θ + η) s t ↔
      ∃ r : U'.left ⟶ Y',
        IsRestrictedPerturbation g' h' iX iY h a U' η s r ∧
          IsRestrictedPerturbation g' h' iX iY h a U' θ r t)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.restricted_act_naturality :
    ∀ {S : Scheme.{u}} {Z Z' X X' Y Y' : AlgebraicSpace S}
      (iZ : Z ⟶ Z') (iX : X ⟶ X')
    (iY : Y ⟶ Y') (h : Y ⟶ Z) (h' : Y' ⟶ Z') (g' : X' ⟶ Z') (a : X ⟶ Y)
    [IsThickening iZ] [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqY : IsPullback h iY iZ h') (sqX : CommSq (a ≫ h) iX iZ g')
    {U' V' : spacesEtaleSite X'} (f : V' ⟶ U')
    (θ : parameterHom h iX (𝟙 Y) a U') (s t : U'.left ⟶ Y')
    (hst : IsRestrictedPerturbation g' h' iX iY h a U' θ s t),
    IsRestrictedPerturbation g' h' iX iY h a V'
      (restrictParameter h iX (𝟙 Y) a f θ) (restrictHom f s) (restrictHom f t))

-- The acting sheaf is the canonical parameter sheaf specialized to the closed base.
section
variable {S : Scheme.{u}} {Z X X' Y : AlgebraicSpace S}
    (h : Y ⟶ Z) (iX : X ⟶ X') (a : X ⟶ Y) [IsFirstOrderThickening iX]

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.parameterSheaf h iX (𝟙 Y) a :
  Sheaf (spacesEtaleTopology X') (Type (u + 1)))
end
