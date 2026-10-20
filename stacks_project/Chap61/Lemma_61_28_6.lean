module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.SheafCompleteness
import StacksCheckRecall

/-!
# Lemma 61.28.6

A derived-complete sheaf of `Λ`-modules on `X_proétale` vanishes if it
vanishes modulo a finitely generated ideal.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProetaleDerived
  (constantCoefficientRing toConstantModuleFunctor constantCoefficientIdeal)
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt
namespace DerivedComplete

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify (ProEt.topology X) (ModuleCat.{w} Λ)]
variable [HasWeakSheafify (ProEt.topology X) CommRingCat.{w}]
variable [HasWeakSheafify (ProEt.topology X) RingCat.{w}]
variable [HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{w}]
variable [(ProEt.topology X).WEqualsLocallyBijective RingCat.{w}]
variable [(ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(ProEt.topology X).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [(ProEt.topology X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [(ProEt.topology X).PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{u + 1, w}]
variable [LocallySmall
    (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
variable [WellPowered
    (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]

/- Lemma 61.28.6: a derived-complete sheaf vanishes if its quotient by a
finitely generated ideal vanishes. -/
@[stacks 09BY] #check
  (AlgebraicGeometry.Scheme.ProEt.DerivedComplete.quotient_isZero :
    ∀ (I : Ideal Λ), I.FG → ∀ (F : Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)),
      AlgebraicGeometry.Scheme.ProEt.DerivedComplete.IsDerivedComplete I F →
      IsZero (CategoryTheory.Sheaf.IdealPower.quotient I F 1) → IsZero F)

end DerivedComplete
end AlgebraicGeometry.Scheme.ProEt
