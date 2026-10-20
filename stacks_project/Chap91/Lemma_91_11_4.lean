module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.RelativeLift
import StacksCheckRecall

/-!
# Relative lifts of maps of modules along a strict first-order thickening

In Situation 91.9.1, after identifying underlying topoi, if `G'` is flat over
`O_{B'}` and `(f, f')` is strict, then the type of `O'`-linear lifts of an
`O`-linear map `φ : i^* F' ⟶ i^* G'` is, if nonempty, a principal homogeneous
space under Hom_O(F, f^* J ⊗_O G).
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.ChangeOfRings
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
variable {OB' OB O' O : Sheaf J CommRingCat.{max u v}}
variable {π : O' ⟶ O} {τ : OB' ⟶ OB}
variable [IsFirstOrderThickening π] [IsFirstOrderThickening τ]
variable [(restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable (f : OB ⟶ O) [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable (f' : OB' ⟶ O') (hcomm : f' ≫ π = τ ≫ f)
variable (F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J O')
variable (φ : (extendScalars (ringSheafMap π)).obj F' ⟶
    (extendScalars (ringSheafMap π)).obj G')
variable [hflatThickened : IsFlat OB' ((restrictionAlong f').obj G')]

#check (SheafOfModules.RingedSite.FirstOrderThickening.canonicalMap_isIso_of_isFlat
  f f' hcomm G' :
  IsStrict f f' hcomm → IsIso (canonicalMap π f f' hcomm G'))

/- Lemma 91.11.4: Let `(f, f')` be a morphism of first-order thickenings as in
Situation 91.9.1. Let `F'`, `G'` be `O'`-modules and set `F = i^* F'` and
`G = i^* G'`. Let `φ : F ⟶ G` be an `O`-linear map. Assume that `G'` is flat
over `O_{B'}` and that `(f, f')` is a strict morphism of thickenings. The type
of lifts of `φ` to an `O'`-linear map `φ' : F' ⟶ G'` is, if nonempty, a
principal homogeneous space under Hom_O(F, G ⊗_O f^* J), equivalently
Hom_O(F, f^* J ⊗_O G) via the symmetric monoidal swap. -/
@[stacks 08MR]
#check (SheafOfModules.RingedSite.FirstOrderThickening.lift_isEmpty_or_addTorsor_tensor
  f f' hcomm F' G' φ :
  IsStrict f f' hcomm →
    IsEmpty (Lift F' G' φ) ∨
      ∃ t : AddTorsor
          ((extendScalars (ringSheafMap π)).obj F' ⟶
            moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
              ((extendScalars (ringSheafMap π)).obj G'))
          (Lift F' G' φ),
        ∀ (α : (extendScalars (ringSheafMap π)).obj F' ⟶
              moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
                ((extendScalars (ringSheafMap π)).obj G'))
            (β : F' ⟶ idealMulO' π G') (ℓ : Lift F' G' φ),
          (extendScalars (ringSheafMap π)).map β =
              α ≫ canonicalMap π f f' hcomm G' →
            t.toAddAction.toAddSemigroupAction.toVAdd.vadd α ℓ =
              Lift.vadd F' G' φ β ℓ)

/- Any two lifts of `φ` differ by a unique `O`-module morphism
`F ⟶ f^* J ⊗_O G`, acting by the Lemma 91.11.1 translation after
postcomposition with `canonicalMap`. -/
#check (SheafOfModules.RingedSite.FirstOrderThickening.Lift.existsUnique_vsub_tensor
  f f' hcomm F' G' φ :
  IsStrict f f' hcomm → ∀ (ℓ₁ ℓ₂ : Lift F' G' φ),
    ∃! α :
      (extendScalars (ringSheafMap π)).obj F' ⟶
        moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
          ((extendScalars (ringSheafMap π)).obj G'),
      ∃ β : F' ⟶ idealMulO' π G',
        (extendScalars (ringSheafMap π)).map β =
            α ≫ canonicalMap π f f' hcomm G' ∧
          Lift.vadd F' G' φ β ℓ₂ = ℓ₁)

end SheafOfModules.RingedSite.FirstOrderThickening
