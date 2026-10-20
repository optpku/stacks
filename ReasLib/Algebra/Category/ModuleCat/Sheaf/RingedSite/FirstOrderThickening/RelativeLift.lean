module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.Lift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.Flat

/-!
# Relative lifts of module maps across a strict first-order thickening square

For a target module flat over the thickened base, lifts of a map between reductions
form, when nonempty, a torsor under maps into the pulled-back base ideal tensored
with the reduced target. The symmetric monoidal braiding canonically identifies
this tensor product `f^* J ⊗_O G` with `G ⊗_O f^* J`.
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

namespace Lift

include hflatThickened in
/-- For a strict square and a target flat over the thickened base, any two lifts
differ by a unique map into the pulled-back base ideal tensored with the reduced
target. Its composite with the canonical comparison is the scalar extension of
a map into the reduction kernel whose translation carries one lift to the other. -/
theorem existsUnique_vsub_tensor (hstrict : IsStrict f f' hcomm)
    (ℓ₁ ℓ₂ : Lift F' G' φ) :
    ∃! α :
      (extendScalars (ringSheafMap π)).obj F' ⟶
        moduleTensor ((extendScalars (ringSheafMap f)).obj (ideal τ))
          ((extendScalars (ringSheafMap π)).obj G'),
      ∃ β : F' ⟶ idealMulO' π G',
        (extendScalars (ringSheafMap π)).map β =
            α ≫ canonicalMap π f f' hcomm G' ∧
          vadd F' G' φ β ℓ₂ = ℓ₁ := sorry

end Lift

include hflatThickened in
/-- For a strict square and a target flat over the thickened base, lifts are empty
or form an additive torsor under maps into the pulled-back base ideal tensored
with the reduced target. Translation agrees with addition of maps into the
reduction kernel through the canonical comparison. -/
theorem lift_isEmpty_or_addTorsor_tensor (hstrict : IsStrict f f' hcomm) :
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
              Lift.vadd F' G' φ β ℓ := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
