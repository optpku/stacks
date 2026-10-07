module

public import Mathlib.Data.PNat.Basic
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.Algebra.Module.Submodule.DirectedColimit

/-!
# Directed systems of ideal-power annihilator stages

This leaf owns the canonical positive-power stage diagram attached to an ideal and a module.
The stage objects use `Ideal.powerAnnihilatedSubmodule`; the source-facing name
`Ideal.powerTorsion` is the concise finite-stage notation in the predicate leaf. The colimit
and supremum interfaces are delegated to the generic directed-submodule support.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The `ℕ+`-indexed `ModuleCat R` diagram of submodules annihilated by powers of `I`. -/
noncomputable def powerAnnihilatedDiagram (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] : ℕ+ ⥤ ModuleCat R :=
  Submodule.directedDiagram
    (fun n : ℕ+ ↦ I.powerAnnihilatedSubmodule M (n : ℕ))
    (fun n m h ↦
      I.powerAnnihilatedSubmodule_mono M ((PNat.coe_le_coe n m).2 h))

/-- Every transition in `powerAnnihilatedDiagram` is the canonical subtype inclusion. -/
@[simp]
theorem powerAnnihilatedDiagram_map
    {n m : ℕ+} (f : n ⟶ m) :
    (powerAnnihilatedDiagram (R := R) I M).map f =
      ModuleCat.ofHom
        (Submodule.inclusion
          (I.powerAnnihilatedSubmodule_mono M
            ((PNat.coe_le_coe n m).2 (leOfHom f)))) := sorry

/-- The positive-power annihilator stages form a directed family under inclusion. -/
theorem powerAnnihilatedStages_directed (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    Directed (· ≤ ·)
      (fun n : ℕ+ ↦ I.powerAnnihilatedSubmodule M (n : ℕ)) := sorry

/-- The supremum of the positive-power annihilator stages, as a submodule of `M`. -/
abbrev powerAnnihilatedStagesSup (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] : Submodule R M :=
  ⨆ n : ℕ+, I.powerAnnihilatedSubmodule M (n : ℕ)

/-- The positive-power stage supremum is the canonical `I`-primary component. -/
theorem powerAnnihilatedStagesSup_eq_primaryComponent (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    powerAnnihilatedStagesSup I M = Ideal.primaryComponent M I := sorry

/-- The positive-power annihilator stages exhaust an `I`-power torsion module. -/
theorem powerAnnihilatedStagesSup_eq_top (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M]
    (hM : Module.IsIdealPowerTorsion I M) :
    powerAnnihilatedStagesSup I M = ⊤ := sorry

/-- The canonical cocone from the positive-power annihilator stages into their supremum. -/
noncomputable def powerAnnihilatedStagesSupCocone (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    Cocone (powerAnnihilatedDiagram I M) :=
  Submodule.directedSupCocone
    (fun n : ℕ+ ↦ I.powerAnnihilatedSubmodule M (n : ℕ))
    (fun n m h ↦
      I.powerAnnihilatedSubmodule_mono M ((PNat.coe_le_coe n m).2 h))

/-- The supremum cocone of the positive-power annihilator stages is a colimit cocone. -/
noncomputable def powerAnnihilatedStagesSupCoconeIsColimit (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    IsColimit (powerAnnihilatedStagesSupCocone I M) :=
  Submodule.directedSupCocone_isColimit
    (fun n : ℕ+ ↦ I.powerAnnihilatedSubmodule M (n : ℕ))
    (fun n m h ↦
      I.powerAnnihilatedSubmodule_mono M ((PNat.coe_le_coe n m).2 h))
    (powerAnnihilatedStages_directed I M)

/-- If `M` is `I`-power torsion, the positive-power annihilator diagram has ambient module as its
colimit.  The explicit `HasColimit` parameter keeps this API universe-polymorphic. -/
noncomputable def powerAnnihilatedDiagramColimitIsoOfSupEqTop (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M]
    (hSup : powerAnnihilatedStagesSup I M = ⊤)
    [HasColimit (powerAnnihilatedDiagram I M)] :
    colimit (powerAnnihilatedDiagram I M) ≅ ModuleCat.of R M :=
  Submodule.directedColimitIso
    (fun n : ℕ+ ↦ I.powerAnnihilatedSubmodule M (n : ℕ))
    (fun n m h ↦
      I.powerAnnihilatedSubmodule_mono M ((PNat.coe_le_coe n m).2 h))
    (powerAnnihilatedStages_directed I M)
    hSup

/-- If `M` is `I`-power torsion, the positive-power annihilator diagram has ambient module as its
colimit.  The explicit `HasColimit` parameter keeps this API universe-polymorphic. -/
noncomputable def powerAnnihilatedDiagramColimitIso (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M]
    (hM : Module.IsIdealPowerTorsion I M)
    [HasColimit (powerAnnihilatedDiagram I M)] :
    colimit (powerAnnihilatedDiagram I M) ≅ ModuleCat.of R M :=
  powerAnnihilatedDiagramColimitIsoOfSupEqTop I M
    (powerAnnihilatedStagesSup_eq_top I M hM)

/-- The colimit comparison restricts on each positive-power stage to its ambient subtype
inclusion. -/
@[reassoc]
theorem powerAnnihilatedDiagramColimitIso_hom_ι (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M]
    (hM : Module.IsIdealPowerTorsion I M)
    [HasColimit (powerAnnihilatedDiagram I M)] (n : ℕ+) :
    colimit.ι (powerAnnihilatedDiagram I M) n ≫
        (powerAnnihilatedDiagramColimitIso I M hM).hom =
      ModuleCat.ofHom (I.powerAnnihilatedSubmodule M (n : ℕ)).subtype := sorry

end Ideal
