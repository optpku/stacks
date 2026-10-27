/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Over
public import ReasLib.AlgebraicGeometry.FormalSpectrum.AlgebraMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlongSubspace.Types
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType

/-!
# Noetherianity and finite type of affine formal spectra

Finite type of the special fiber of a complete algebra over a Noetherian ring
implies local Noetherianity of its formal spectrum and local finite type of the
induced morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicSpace FormalAlgebraicSpace AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The completion of `Spec(A)` along `Spec(A ⧸ I)` is locally Noetherian when
`A` is Noetherian. -/
instance instIsLocallyNoetherian_completionAlongIdeal {A : Type u} [CommRing A]
    [IsNoetherianRing A] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A) :
    IsLocallyNoetherian (completionAlongSubspace (closedImmersion hA I)) := by
  refine @AlgebraicSpace.isLocallyNoetherian_completionAlongSubspace S _ _ ?_
    (closedImmersion hA I) inferInstance
  exact @AlgebraicSpace.instIsLocallyNoetherian_ofOver S (Over.mk hA) (by
    change AlgebraicGeometry.IsLocallyNoetherian (Spec (.of A))
    infer_instance)

/-- Completeness together with finite type of the special fiber
`A ⧸ I → B ⧸ IB` makes the completion of `Spec(B)` along `V(IB)` locally
Noetherian. -/
instance instIsLocallyNoetherian_completionAlongIdeal_algebra
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [Algebra A B]
    (I : Ideal A) [IsAdicComplete I B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))]
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    IsLocallyNoetherian
      (completionAlongSubspace
        (closedImmersion
          (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
          (I.map (algebraMap A B)))) :=
  sorry

/-- The morphism of sheafy formal spectra induced by an `I`-adically complete
algebra over a Noetherian ring is locally of finite type, given finite type of
the special fiber. -/
instance locallyOfFiniteType_spfAdicCompletionMap
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [Algebra A B]
    (I : Ideal A) [IsAdicComplete I A] [IsAdicComplete I B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))]
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    LocallyOfFiniteType (spfAdicCompletionMap B hA I) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
