module

public import Mathlib.Algebra.Torsor.Defs
public import stacks_project.Chap91.Lemma_91_10_1_Compatible
import Mathlib.Tactic.CrossRefAttribute

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
variable (F G : Extension π) (φ : F.quot ⟶ G.quot) (ψ : F.kernel ⟶ G.kernel)

/-- Lemma 91.10.1 (1): on a first-order thickening of ringed topoi, after identifying
underlying topoi as a same-site locally surjective square-zero map π : 𝒪' ⟶ 𝒪, any
𝒪'-module map ℱ' ⟶ 𝒢' compatible with φ : ℱ ⟶ 𝒢 and ψ : 𝒦 ⟶ ℒ makes the square
infMap of ℱ', moduleTensorMap (𝟙 (idealModule hπ)) φ, ψ, and infMap of 𝒢' commute. -/
@[stacks 08MC]
theorem infMap_commSq (hπ : KernelIdeal.IsSquareZero π) [Sheaf.IsLocallySurjective π]
    (f : CompatibleMap F G φ ψ) :
    CommSq (infMap hπ F) (moduleTensorMap (𝟙 (idealModule hπ)) φ) ψ (infMap hπ G) :=
  sorry

/-- Lemma 91.10.1 (2): on a first-order thickening of ringed topoi, after identifying
underlying topoi as a same-site locally surjective square-zero map π : 𝒪' ⟶ 𝒪, the type
of 𝒪'-module maps ℱ' ⟶ 𝒢' compatible with φ : ℱ ⟶ 𝒢 and ψ : 𝒦 ⟶ ℒ is, if nonempty, a
principal homogeneous space under Hom_𝒪(ℱ, ℒ). -/
@[stacks 08MC]
theorem compatibleMap_isEmpty_or_addTorsor (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    IsEmpty (CompatibleMap F G φ ψ) ∨
      Nonempty (AddTorsor (F.quot ⟶ G.kernel) (CompatibleMap F G φ ψ)) :=
  sorry

end SheafOfModules.RingedSite.FirstOrderThickening
