module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.HomologyZero
import StacksCheckRecall

/-!
# Degree-zero homology of the cotangent complex of a morphism of ring sheaves

Lemma 92.18.6 identifies the cohomology sheaf `H^0(L(φ))` with the sheaf of relative
differentials `Ω(φ)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.CotangentComplex

universe u

/- Lemma 92.18.6. Let `C` be a site. Let `A ⟶ B` be a homomorphism of sheaves of rings
on `C`. Then `H^0(L(φ)) = Ω(φ)`. -/
@[stacks 08UR] #check (SheafOfModules.RingedSite.CotangentComplex.homologyZeroIso :
    ∀ {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
      [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
      [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
      [HasWeakSheafify J CommRingCat.{u}]
      [HasWeakSheafify J AddCommGrpCat.{u}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
      {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B),
      L(φ).homology 0 ≅ Ω(φ))

#check (SheafOfModules.RingedSite.CotangentComplex.homologyZeroIso_hom :
    ∀ {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
      [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
      [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
      [HasWeakSheafify J CommRingCat.{u}]
      [HasWeakSheafify J AddCommGrpCat.{u}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
      {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B),
      (CotangentComplex.homologyZeroIso φ).hom = CotangentComplex.homologyZeroMap φ)
