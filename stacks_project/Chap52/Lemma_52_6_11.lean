/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.FiniteTypeCech
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived

open SheafOfModules.RingedSite.ExtendedCech

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/- Lemma 52.6.11: a finite-type ideal sheaf admits a derived Čech object mapping to the
structure sheaf. On every slice where a finite family generates the restricted ideal sheaf,
this object restricts to the corresponding extended alternating Čech complex, compatibly with
the projections to the local structure sheaf. -/
@[stacks 099E] #check (RingedSite.Hom.ModuleDerived.existsCechModelOfFiniteType :
  ∀ (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType],
    ∃ (K : RingedSiteDerived J O)
      (η : K ⟶
        (@DerivedCategory.singleFunctor _ _
          (moduleCategoryAbelian (J := J) (𝒪 := O))
          (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O)) (0 : ℤ)).obj
          (unitModule J O)),
      ∀ (U : C) (r : ℕ)
        (f : Fin r → (unitModule (J.over U) (O.over U)).sections),
        generatedIdeal f = imageSubobject (I.arrow.over U) →
          ∃ e : derived f ≅
              (localizedRestrictionDerived.{u} (RingedSite.ofCommRingSheaf J O) U).obj K,
            e.hom ≫ localizedMapToUnit U η = projection f)

end RingedSite.Hom.ModuleDerived
