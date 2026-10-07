module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module sheafification and localization of a ringed site

This file is the commutative-ringed-site spelling of the coefficient-generic compatibility
between module sheafification and restriction to a slice.  All comparison data is owned by
`SheafOfModules.Localization.ModuleSheafification`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ModuleSheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v}) (U : C)
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Module sheafification commutes with restriction to a slice site. -/
@[stacks 04IX "module sheafification commutes with localized restriction"]
noncomputable abbrev overIso
    (P : PresheafOfModules.{max u v} (ringSheaf J O).obj) :
    ((moduleSheafification O).obj P).over U ≅
      (moduleSheafification (O.over U)).obj (P.over U) :=
  _root_.SheafOfModules.Localization.ModuleSheafification.overIso
    (ringSheaf J O) U P

/-- The localized sheafification comparison carries the restricted ambient sheafification unit
to the sheafification unit on the slice. -/
theorem unitToVal_overIso_hom
    (P : PresheafOfModules.{max u v} (ringSheaf J O).obj) :
    PresheafOfModules.Hom.over (moduleSheafificationUnitToVal O P) U ≫
        (overIso O U P).hom.val =
      moduleSheafificationUnitToVal (O.over U) (P.over U) := sorry

/-- Restriction to a slice and module sheafification commute naturally. -/
@[stacks 04IX "natural module-sheafification localization comparison"]
noncomputable abbrev overNatIso :
    moduleSheafification O ⋙
        SheafOfModules.overFunctor (ringSheaf J O) U ≅
      PresheafOfModules.overFunctor (ringSheaf J O).obj U ⋙
        moduleSheafification (O.over U) :=
  _root_.SheafOfModules.Localization.ModuleSheafification.overNatIso
    (ringSheaf J O) U

end SheafOfModules.RingedSite.ModuleSheafification
