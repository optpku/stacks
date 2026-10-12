/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization
import StacksCheckRecall

/-!
# Lemma 18.19.2

Compatibility facade for extension from a localized site.  The left adjoint of restriction and
its canonical construction by presheaf-module pullback followed by sheafification are owned by
`ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.Localization

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J RingCat.{u}) (U : C)

/- Lemma 18.19.2 (1): extension `j_{U!}` from the slice site is left adjoint to restriction
`j_U^*`. -/
@[stacks 03DI "(1)"]
#check
  (lowerShriekRestrictionAdj R U :
    (lowerShriek R U :
      SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} R) ⊣
      (restriction R U :
        SheafOfModules.{u} R ⥤ SheafOfModules.{u} (R.over U)))

variable (G : SheafOfModules.{u} (R.over U)) (F : SheafOfModules.{u} R)

/- Lemma 18.19.2 (1), Hom form: the adjunction gives the canonical morphism equivalence. -/
#check
  (lowerShriekHomEquiv R U G F :
    ((lowerShriek R U).obj G ⟶ F) ≃
      (G ⟶ (restriction R U).obj F))

/- Lemma 18.19.2 (2): `j_{U!}` is canonically the presheaf-module pullback construction followed
by ambient sheafification. -/
@[stacks 03DI "(2)"]
#check
  (lowerShriekSheafificationIso R U :
    (lowerShriek R U :
      SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} R) ≅
      lowerShriekSheafification R U)

end SheafOfModules.Localization

namespace PresheafOfModules.Localization

variable {C : Type u} [SmallCategory C]
variable (R : Cᵒᵖ ⥤ RingCat.{u}) (U : C)
variable (G : PresheafOfModules ((Over.forget U).op ⋙ R)) (V : C)

/- Lemma 18.19.2 (2), explicit formula: before sheafification, lower shriek at `V` is the
coproduct indexed by arrows `V ⟶ U`; the shared API states this as invertibility of the
canonical summandwise map. -/
@[stacks 03DI "(2), coproduct formula"]
#check
  (coproductToLowerShriek_isIso R U G V :
    IsIso (coproductToLowerShriek R U G V))

end PresheafOfModules.Localization
