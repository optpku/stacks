module

public import stacks_project.Chap61.Definition_61_29_1_Derived
public import stacks_project.Chap61.Lemma_61_28_3_Quotient
import Mathlib.Tactic.CrossRefAttribute

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

/-- A sheaf of `Λ`-modules on `X_proétale` is derived complete with respect to `I`
when the degree-zero image of `(toConstantModuleFunctor X Λ).obj F` is derived
complete with respect to `constantCoefficientIdeal I`. -/
abbrev IsDerivedComplete (I : Ideal Λ) (F : Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) :
    Prop :=
  IsDerivedCompleteWithRespectTo
    ((DerivedCategory.singleFunctor
        (RingedSite.ModuleCat
          (RingedSite.ofCommRingSheaf (ProEt.topology X) (constantCoefficientRing X Λ)))
        (0 : ℤ)).obj
      ((toConstantModuleFunctor X Λ).obj F))
    (constantCoefficientIdeal I)

/-- Unfolding of `IsDerivedComplete` as Chap52 completeness of the constant-ringed-site
degree-zero image. -/
theorem isDerivedComplete_iff
    (I : Ideal Λ) (F : Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) :
    IsDerivedComplete I F ↔
      IsDerivedCompleteWithRespectTo
        ((DerivedCategory.singleFunctor
            (RingedSite.ModuleCat
              (RingedSite.ofCommRingSheaf (ProEt.topology X)
                (constantCoefficientRing X Λ)))
            (0 : ℤ)).obj
          ((toConstantModuleFunctor X Λ).obj F))
        (constantCoefficientIdeal I) :=
  sorry

/-- Lemma 61.28.6: if `F` is a derived-complete sheaf of `Λ`-modules on `X_proétale`
and `I ⊆ Λ` is finitely generated with `F / I F = 0`, then `F = 0`. -/
@[stacks 09BY]
theorem quotient_isZero (I : Ideal Λ) (hI : I.FG)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))
    (hF : IsDerivedComplete I F)
    (hquot : IsZero (IdealPower.quotient I F 1)) :
    IsZero F :=
  sorry

/-- Under derived completeness and finite generation of `I`, vanishing of `F / I F`
is equivalent to vanishing of `F`. -/
theorem quotient_isZero_iff (I : Ideal Λ) (hI : I.FG)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{w} Λ))
    (hF : IsDerivedComplete I F) :
    IsZero (IdealPower.quotient I F 1) ↔ IsZero F :=
  sorry

end DerivedComplete
end AlgebraicGeometry.Scheme.ProEt
