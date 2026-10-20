module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completion.Koszul
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

universe u

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/- Lemma 52.6.9: derived completion along a finitely globally generated ideal is the
homotopy limit of derived tensor products with the ordinary powered Koszul complexes. -/
@[stacks 0A0E] #check
  (RingedSite.Hom.ModuleDerived.derivedCompletion_isHomotopyLimit :
    ∀ {r : ℕ} (I : Subobject (unitModule J O))
      (f : Fin r → (unitModule J O).sections)
      (hgen : ExtendedCech.generatedIdeal f = I)
      (K Khat : RingedSiteDerived.{u, u, u, u} J O) (η : K ⟶ Khat)
      (hη : RingedSite.Hom.ModuleDerived.IsDerivedCompletion.{u, u, u, u} I η),
      HomotopyLimit.IsOf
        (RingedSite.Hom.ModuleDerived.poweredKoszulChainTensorTower f K) Khat)
