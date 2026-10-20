/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.Artinian.Residue
import StacksCheckRecall

/-!
# Lemma 10.54.4
@stack 07DT
-/

@[expose] public section

universe u v

open IsLocalRing

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsArtinianRing S] [IsLocalRing S]

/- Lemma 10.54.4 (1) (07DT): finiteness of a map to an Artinian local ring is detected on the
residue field. -/
@[stacks 07DT "(1)"]
#check (RingHom.finite_iff_residue_finite (R := R) (S := S) :
  ∀ f : R →+* S, f.Finite ↔ ((residue S).comp f).Finite)

/- Lemma 10.54.4 (2) (07DT): finite type of a map to an Artinian local ring is detected on the
residue field. -/
@[stacks 07DT "(2)"]
#check (RingHom.finiteType_iff_residue_finiteType (R := R) (S := S) :
  ∀ f : R →+* S, f.FiniteType ↔ ((residue S).comp f).FiniteType)

/- Lemma 10.54.4 (3) (07DT): essential finite type of a map to an Artinian local ring is detected
on the residue field. -/
@[stacks 07DT "(3)"]
#check (RingHom.essFiniteType_iff_residue_essFiniteType (R := R) (S := S) :
  ∀ f : R →+* S, f.EssFiniteType ↔ ((residue S).comp f).EssFiniteType)

end
