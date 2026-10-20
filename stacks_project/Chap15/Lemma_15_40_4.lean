/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalRing.ResidueField.Cotangent.JacobiZariski.Adic

/-!
# Lemma 15.40.4

@stack 0DYH

The reusable residue-field Jacobi--Zariski API is owned by
`ReasLib.RingTheory.LocalRing.ResidueField.Cotangent.JacobiZariski` and its
`Row` and `Adic` companion leaves.
-/

@[expose] public section

/- Lemma 15.40.4 (0DYH): for a local homomorphism of Noetherian local rings that is formally
smooth in the maximal-ideal-adic topology, the residue-field Jacobi--Zariski row
`0 → H1Cotangent A (ResidueField B) → CotangentSpace B →
  (ResidueField B) ⊗[B] Ω[B⁄A] → Ω[ResidueField B⁄A] → 0`
is exact.  The tensor term uses the library orientation, canonically equivalent
to the source's `Ω[B⁄A] ⊗[B] ResidueField B`.  The tagged check uses the
same-universe `ModuleCat` facade; the raw map checks below retain arbitrary
universes. -/
@[stacks 0DYH "formal-smooth residue-field Jacobi--Zariski exact row"]
#check @Algebra.H1Cotangent.ResidueField.row_exact_of_formallySmoothAdic

/- The universe-polymorphic source row is recovered from these four atomic facts:
injectivity of the first arrow, exactness at both middle terms, and surjectivity
of the last nonzero arrow. -/
#check @Algebra.H1Cotangent.ResidueField.injective_of_formallySmoothAdic
#check @Algebra.H1Cotangent.ResidueField.toCotangent
#check @Algebra.H1Cotangent.ResidueField.toCotangent_exact
#check @IsLocalRing.ResidueField.conormal_exact
#check @IsLocalRing.ResidueField.mapBaseChange_surjective

/- The categorical facade reduces exactness of the full row to injectivity of its first arrow. -/
#check @Algebra.H1Cotangent.ResidueField.row_exact_iff
