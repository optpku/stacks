module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree

@[expose] public section

/-!
# Stages of Semi-Free Filtrations as Subobjects

This leaf records the ambient-subobject presentation of stages in a semi-free
filtration.  It is independent of the compactness and derived-category
arguments that use finite subfiltrations.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CochainComplex.SemiFreeFiltration

variable {A : Type u} [Ring A]

/-- The `n`th stage of a semi-free filtration, regarded as a subobject of the ambient complex. -/
noncomputable def stageSubobject {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℕ) [Mono (F.coconeApp n)] : Subobject P :=
  Subobject.mk (F.coconeApp n)

/-- The underlying object of `stageSubobject F n` is canonically the original filtration stage. -/
noncomputable def stageSubobjectIso {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℕ) [Mono (F.coconeApp n)] :
    Subobject.underlying.obj (F.stageSubobject n) ≅ F.stage n :=
  Subobject.underlyingIso (F.coconeApp n)

/-- Rewriting the subobject arrow through `stageSubobjectIso` recovers the original cocone leg. -/
theorem stageSubobjectIso_inv_arrow {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℕ) [Mono (F.coconeApp n)] :
    (F.stageSubobjectIso n).inv ≫ (F.stageSubobject n).arrow = F.coconeApp n := sorry

/-- The forward map of `stageSubobjectIso` identifies the original cocone leg with the packaged
subobject arrow. -/
theorem stageSubobjectIso_hom_comp_coconeApp {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℕ) [Mono (F.coconeApp n)] :
    (F.stageSubobjectIso n).hom ≫ F.coconeApp n = (F.stageSubobject n).arrow := sorry

/-- Consecutive filtration stages define increasing ambient subobjects. -/
theorem stageSubobject_le_succ {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℕ)
    [Mono (F.coconeApp n)] [Mono (F.coconeApp (n + 1))] :
    F.stageSubobject n ≤ F.stageSubobject (n + 1) := sorry

/-- The canonical comparison of consecutive stage subobjects is the original filtration map after
identifying their underlying objects with the raw stages. -/
theorem stageSubobjectIso_inv_comp_ofLE {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℕ)
    [Mono (F.coconeApp n)] [Mono (F.coconeApp (n + 1))] :
    (F.stageSubobjectIso n).inv ≫
        Subobject.ofLE (F.stageSubobject n) (F.stageSubobject (n + 1))
          (F.stageSubobject_le_succ n) =
      F.inclusion n ≫ (F.stageSubobjectIso (n + 1)).inv := sorry

/-- The quotient map from the next stage subobject to the raw successive quotient. -/
noncomputable def stageQuotientMap {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℕ) [Mono (F.coconeApp (n + 1))] :
    Subobject.underlying.obj (F.stageSubobject (n + 1)) ⟶ cokernel (F.inclusion n) :=
  (F.stageSubobjectIso (n + 1)).hom ≫ cokernel.π (F.inclusion n)

/-- Transporting `stageQuotientMap` through `stageSubobjectIso` recovers the raw cokernel
projection. -/
theorem stageSubobjectIso_inv_comp_stageQuotientMap {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℕ) [Mono (F.coconeApp (n + 1))] :
    (F.stageSubobjectIso (n + 1)).inv ≫ F.stageQuotientMap n =
      cokernel.π (F.inclusion n) := sorry

/-- The preceding stage subobject maps to zero under the quotient map of the next stage. -/
theorem stageSubobject_ofLE_comp_stageQuotientMap_eq_zero {P : ModuleCat.DGMod A}
    (F : SemiFreeFiltration P) (n : ℕ)
    [Mono (F.coconeApp n)] [Mono (F.coconeApp (n + 1))] :
    Subobject.ofLE (F.stageSubobject n) (F.stageSubobject (n + 1))
        (F.stageSubobject_le_succ n) ≫ F.stageQuotientMap n = 0 := sorry

end CochainComplex.SemiFreeFiltration
