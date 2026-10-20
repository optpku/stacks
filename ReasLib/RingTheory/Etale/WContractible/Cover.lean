/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.WContractible
public import ReasLib.RingTheory.RingHom.IndEtale.Basic

/-!
# W-contractible covers of commutative rings

Every commutative ring admits a faithfully flat ind-étale extension with
w-contractible codomain.
-/

@[expose] public section

universe u v

namespace IsWContractibleRing

/-- Every commutative ring admits a faithfully flat ind-étale ring map with
w-contractible codomain. -/
theorem exists_faithfullyFlat_indEtale (A : Type u) [CommRing A] :
    ∃ (D : Type u) (_ : CommRing D) (f : A →+* D),
      f.FaithfullyFlat ∧ f.IndEtale ∧ IsWContractibleRing.{u, v} D :=
  sorry

/-- There exists a faithfully flat ind-étale `A`-algebra whose underlying ring
is w-contractible. -/
theorem exists_faithfullyFlat_indEtale_algebra (A : Type u) [CommRing A] :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      Module.FaithfullyFlat A D ∧ (algebraMap A D).IndEtale ∧
        IsWContractibleRing.{u, v} D :=
  sorry

end IsWContractibleRing
