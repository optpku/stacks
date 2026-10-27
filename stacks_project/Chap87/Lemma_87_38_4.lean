/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.AdicCompletion
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.LocalWeaklyAdic
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 87.38.4. Completion of an affine scheme along a closed subscheme is
weakly adic, is the formal spectrum of its adic completion and adic* under finite
generation, and is Noetherian when the affine scheme is Noetherian. -/
@[stacks 0GXX] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.completionAlongIdeal_types :
    ∀ {S : Scheme.{u}} {A : Type u} [CommRing A]
      [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
      (structureHom : Spec (.of A) ⟶ S) (I : Ideal A),
      IsWeaklyAdic (spfAdicCompletionSheaf structureHom I).obj ∧
        (I.FG →
          IsAdic (I.map (algebraMap A (AdicCompletion.WithLimitTopology I))) ∧
            IsIso (toSpfCompletion structureHom I) ∧
              IsAdicStarAffine (spfAdicCompletionSheaf structureHom I).obj) ∧
        (AlgebraicGeometry.IsNoetherian (Spec (.of A)) →
          IsNoetherianAffine (spfAdicCompletionSheaf structureHom I).obj))
