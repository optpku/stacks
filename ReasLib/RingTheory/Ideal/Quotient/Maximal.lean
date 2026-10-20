/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Maximal ideals of a quotient ring

@stack 00G9

This leaf restricts the quotient ideal correspondence to maximal ideals and
records its computation by `comap` and `map`.
-/

@[expose] public section

universe u

namespace Ideal.Quotient

variable {R : Type u} [CommRing R]

/-- Maximal ideals of `R ⧸ I` correspond to maximal ideals of `R` which
contain `I`. -/
@[stacks 00G9 "maximal ideals of a quotient ring"]
def orderIsoOfMaximal (I : Ideal R) :
    {J : Ideal (R ⧸ I) // J.IsMaximal} ≃o
      {K : Ideal R // I ≤ K ∧ K.IsMaximal} :=
  let e : Ideal (R ⧸ I) ≃o Set.Ici I :=
    (Ideal.relIsoOfSurjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective).trans <|
      OrderIso.setCongr _ _ <| by
        ext K
        change (RingHom.ker (Ideal.Quotient.mk I) ≤ K) ↔ I ≤ K
        rw [Ideal.mk_ker]
  { toFun := fun J ↦
      ⟨(e J.1).1, (e J.1).2,
        Ideal.isMaximal_def.2 <|
          IsCoatom.of_isCoatom_coe_Ici <| (OrderIso.isCoatom_iff e J.1).2 <|
            Ideal.isMaximal_def.1 J.2⟩
    invFun := fun K ↦
      ⟨e.symm ⟨K.1, K.2.1⟩,
        Ideal.isMaximal_def.2 <|
          (OrderIso.isCoatom_iff e.symm ⟨K.1, K.2.1⟩).2 <|
            IsCoatom.Ici (Ideal.isMaximal_def.1 K.2.2) K.2.1⟩
    left_inv := fun J ↦ by
      apply Subtype.ext
      simp [e]
    right_inv := fun K ↦ by
      apply Subtype.ext
      simpa [e] using congrArg Subtype.val (e.right_inv ⟨K.1, K.2.1⟩)
    map_rel_iff' := fun {J J'} ↦ e.map_rel_iff }

/-- The forward maximal-ideal correspondence is contraction along the
quotient map. -/
@[simp, stacks 00G9 "contraction formula for quotient maximal ideals"]
theorem orderIsoOfMaximal_apply_val (I : Ideal R)
    (J : {J : Ideal (R ⧸ I) // J.IsMaximal}) :
    (orderIsoOfMaximal I J).1 = Ideal.comap (Ideal.Quotient.mk I) J.1 := by
  rfl

/-- The inverse maximal-ideal correspondence is extension along the quotient
map. -/
@[simp, stacks 00G9 "extension formula for quotient maximal ideals"]
theorem orderIsoOfMaximal_symm_apply_val (I : Ideal R)
    (K : {K : Ideal R // I ≤ K ∧ K.IsMaximal}) :
    ((orderIsoOfMaximal I).symm K).1 =
      Ideal.map (Ideal.Quotient.mk I) K.1 := by
  rfl

end Ideal.Quotient
