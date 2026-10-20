module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.Compatible
import StacksCheckRecall

/-!
# Compatible maps of mixed-scalar extensions on first-order thickenings

On a first-order thickening of ringed topoi, after identifying underlying topoi, a
compatible 𝒪'-module map of mixed-scalar extensions makes the infinitesimal-map square
commute, and the type of such maps is a principal homogeneous space under Hom_𝒪(ℱ, ℒ)
whenever it is nonempty.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}

/- Lemma 91.10.1 (1): compatible maps intertwine the infinitesimal maps. -/
@[stacks 08MC] #check (SheafOfModules.RingedSite.FirstOrderThickening.infMap_commSq :
  (F G : Extension π) → (φ : F.quot ⟶ G.quot) → (ψ : F.kernel ⟶ G.kernel) →
    [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})] →
    [HasWeakSheafify J CommRingCat.{max u v}] →
    [J.WEqualsLocallyBijective CommRingCat.{max u v}] →
    [HasWeakSheafify J AddCommGrpCat.{max u v}] →
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] →
      (hπ : KernelIdeal.IsSquareZero π) → [Sheaf.IsLocallySurjective π] →
      (f : CompatibleMap F G φ ψ) →
        CommSq (infMap hπ F) (moduleTensorMap (𝟙 (idealModule hπ)) φ) ψ (infMap hπ G))

/- Lemma 91.10.1 (2): compatible maps are empty or form an additive torsor. -/
@[stacks 08MC] #check
  (SheafOfModules.RingedSite.FirstOrderThickening.compatibleMap_isEmpty_or_addTorsor :
    (F G : Extension π) → (φ : F.quot ⟶ G.quot) → (ψ : F.kernel ⟶ G.kernel) →
      [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})] →
      [HasWeakSheafify J CommRingCat.{max u v}] →
      [J.WEqualsLocallyBijective CommRingCat.{max u v}] →
      [HasWeakSheafify J AddCommGrpCat.{max u v}] →
      [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] →
        (hπ : KernelIdeal.IsSquareZero π) → [Sheaf.IsLocallySurjective π] →
          IsEmpty (CompatibleMap F G φ ψ) ∨
            Nonempty (AddTorsor (F.quot ⟶ G.kernel) (CompatibleMap F G φ ψ)))

end SheafOfModules.RingedSite.FirstOrderThickening
