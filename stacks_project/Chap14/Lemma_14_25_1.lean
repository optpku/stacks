/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.AlternatingCofaceMapComplex
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Decomposition.Canonical
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Decomposition.Normalized
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Normalized.Equivalence
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Normalized.Exact
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Compat
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Exact
import StacksCheckRecall

/-!
@stack 019I

# Source-facing bridge for Lemma 14.25.1

The quotient-defined normalized cochain complex, its degenerate splitting, exactness, and the
cosimplicial Dold--Kan equivalence are owned by the neutral ReasLib Dold--Kan leaves.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (U : CosimplicialObject A)

/- The canonical degenerate summand is the opposite/unop image of `QInfty`; the older
   `degenerateCochainComplex` declarations below remain source-facing compatibility checks. -/
#check (DoldKan.degenerate.functor (A := A) :
  CosimplicialObject A ⥤ CochainComplex A ℕ)
#check (DoldKan.degenerate.obj U : CochainComplex A ℕ)
#check (DoldKan.degenerate.ι U :
  DoldKan.degenerate.obj U ⟶ (alternatingCofaceMapComplex A).obj U)
#check (DoldKan.degenerate.ρ U :
  (alternatingCofaceMapComplex A).obj U ⟶ DoldKan.degenerate.obj U)
#check (DoldKan.degenerate.ι_comp_ρ U :
  DoldKan.degenerate.ι U ≫ DoldKan.degenerate.ρ U = 𝟙 (DoldKan.degenerate.obj U))
#check DoldKan.degenerate.projector U
#check DoldKan.degenerate.projector_comp_projector U

/- The bundled exact functor is the reusable owner for clause (1). -/
#check (AlgebraicTopology.alternatingCofaceMapComplex.exactFunctor (A := A) :
  CosimplicialObject A ⥤ₑ CochainComplex A ℕ)

/- Lemma 14.25.1 (1): the alternating coface complex functor is exact. -/
@[stacks 019I]
#check ((AlgebraicTopology.alternatingCofaceMapComplex.exactFunctor
    (A := A)).property :
  exactFunctor (CosimplicialObject A) (CochainComplex A ℕ)
    (alternatingCofaceMapComplex A))

#check (AlgebraicTopology.alternatingCofaceMapComplex.preservesFiniteLimits (A := A) :
  PreservesFiniteLimits (alternatingCofaceMapComplex A))

#check (AlgebraicTopology.alternatingCofaceMapComplex.preservesFiniteColimits (A := A) :
  PreservesFiniteColimits (alternatingCofaceMapComplex A))

/- Lemma 14.25.1 (2): the canonical image quotient maps `s(U) ⟶ Q(U)` form a natural
   transformation. The older quotient owner is retained below as a compatibility check. -/
@[stacks 019I]
#check (DoldKan.degenerate.normalized.π.natTrans (A := A) :
  alternatingCofaceMapComplex A ⟶ DoldKan.degenerate.normalized.functor)

@[stacks 019I]
#check (DoldKan.degenerate.normalized.π U :
  (alternatingCofaceMapComplex A).obj U ⟶ DoldKan.degenerate.normalized.obj U)

/- The canonical image quotient is itself the reusable Dold--Kan equivalence and exact functor. -/
#check (DoldKan.degenerate.normalized.equivalence (A := A) :
  CosimplicialObject A ≌ CochainComplex A ℕ)
#check (DoldKan.degenerate.normalized.exactFunctor (A := A) :
  CosimplicialObject A ⥤ₑ CochainComplex A ℕ)
#check ((DoldKan.degenerate.normalized.exactFunctor (A := A)).property :
  exactFunctor (CosimplicialObject A) (CochainComplex A ℕ)
    DoldKan.degenerate.normalized.functor)
#check (DoldKan.degenerate.normalized.π.quasiIso U :
  QuasiIso (DoldKan.degenerate.normalized.π U))

/- The source-facing degreewise-span degenerate model is canonically identified with the
   projector-image model through the shared comparison natural isomorphism. -/
#check (DoldKan.degenerate.comparison.iso U :
  degenerateCochainComplex U ≅ DoldKan.degenerate.obj U)
#check (DoldKan.degenerate.comparison.natIso (A := A) :
  degenerateCochainComplex.functor (A := A) ≅ DoldKan.degenerate.functor)

/- Compatibility owner for the source-facing degreewise-span quotient. -/
@[stacks 019I "Lemma 14.25.1 (2): source quotient presentation"]
#check (normalizedCochainComplex.π.natTrans (A := A) :
  alternatingCofaceMapComplex A ⟶ normalizedCochainComplex.functor)

/- The source quotient and canonical image quotient are compared objectwise and naturally, with
both quotient-map coordinates exposed by the shared owner. -/
#check (DoldKan.degenerate.normalized.comparison.iso U :
  normalizedCochainComplex U ≅ DoldKan.degenerate.normalized.obj U)
#check (DoldKan.degenerate.normalized.comparison.natIso (A := A) :
  normalizedCochainComplex.functor (A := A) ≅
    DoldKan.degenerate.normalized.functor)
#check DoldKan.degenerate.normalized.comparison.π_comp_iso
#check DoldKan.degenerate.normalized.comparison.π_comp_iso_inv

/- Lemma 14.25.1 (3): `s` splits functorially as the degenerate--normalized biproduct. -/
@[stacks 019I]
#check (DoldKan.degenerate.decomposition.splitting (A := A) :
  alternatingCofaceMapComplex A ≅
    (DoldKan.degenerate.functor (A := A)) ⊞
      DoldKan.degenerate.normalized.functor (A := A))

/- Compatibility owner for the source-facing degreewise-span splitting. -/
@[stacks 019I "Lemma 14.25.1 (3): source degenerate-normalized splitting"]
#check (normalizedCochainComplex.splitting (A := A) :
  alternatingCofaceMapComplex A ≅
    (degenerateCochainComplex.functor (A := A)) ⊞ normalizedCochainComplex.functor)

/- The bundled exact functor is the reusable owner for clause (4). -/
#check (normalizedCochainComplex.exactFunctor (A := A) :
  CosimplicialObject A ⥤ₑ CochainComplex A ℕ)

/- Lemma 14.25.1 (4): the normalized cochain complex functor is exact. -/
@[stacks 019I]
#check ((normalizedCochainComplex.exactFunctor (A := A)).property :
  exactFunctor (CosimplicialObject A) (CochainComplex A ℕ)
    normalizedCochainComplex.functor)

/- Lemma 14.25.1 (5): the quotient map `s(U) ⟶ Q(U)` is a quasi-isomorphism. -/
@[stacks 019I]
#check (normalizedCochainComplex.π.quasiIso U :
  QuasiIso (normalizedCochainComplex.π U))

/- Lemma 14.25.1 (6): normalized cochains give the cosimplicial Dold--Kan equivalence. -/
@[stacks 019I]
#check (normalizedCochainComplex.equivalence (A := A) :
  CosimplicialObject A ≌ CochainComplex A ℕ)

end CategoryTheory.CosimplicialObject
