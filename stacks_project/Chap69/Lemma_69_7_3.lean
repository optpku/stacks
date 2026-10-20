/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.OffDiagonalAffineCover
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.OffDiagonalAffineCover
import StacksCheckRecall

/-!
# Lemma 69.7.3

Existence of bounded affine étale covers of off-diagonal quotients and the resulting
vanishing bound for étale cohomology of quasi-coherent modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 69.7.3 (1): Existence of bounded affine étale covers of the off-diagonal quotients. -/
@[stacks 072C] #check (AlgebraicGeometry.AlgebraicSpace.exists_affineEtale_offDiagonalAffineCover :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X],
    ∃ (U : Over S) (f : ofOver U ⟶ X) (d : ℕ),
      AlgebraicGeometry.IsAffine U.left ∧ Etale f ∧ Surjective f ∧ Separated f ∧
        degreesOfFibresBoundedBy f d ∧
        ∀ [Separated f],
          ∃ (Up : Fin (d + 1) → AlgebraicSpace S)
            (q : ∀ p, offDiagonal f (p.val + 1) ⟶ Up p)
            (π : ∀ p, Up p ⟶ X)
            (Vp : Fin (d + 1) → Over S)
            (g : ∀ p, ofOver (Vp p) ⟶ Up p)
            (dp : Fin (d + 1) → ℕ),
            (∀ p, IsFreeQuotient (offDiagonalPermLift f (p.val + 1)) (q p)) ∧
              (∀ p, Etale (π p)) ∧
              (∀ p, q p ≫ π p = offDiagonalToBase f (p.val + 1)) ∧
              (∀ p, AlgebraicGeometry.IsAffine (Vp p).left) ∧
              (∀ p, Etale (g p)) ∧ (∀ p, Surjective (g p)) ∧
              (∀ p, degreesOfFibresBoundedBy (g p) (dp p)))

/- Lemma 69.7.3 (2): Cohomology vanishing for every supplied bounded affine cover. -/
@[stacks 072C] #check (AlgebraicGeometry.AlgebraicSpace.cohomology_isZero_of_offDiagonalAffineCover :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    [AlgebraicGeometry.IsAffine U.left] (f : ofOver U ⟶ X)
    [Etale f] [Surjective f] [Separated f]
    (d : ℕ) (hd : degreesOfFibresBoundedBy f d)
    (Up : Fin (d + 1) → AlgebraicSpace S)
    (q : ∀ p, offDiagonal f (p.val + 1) ⟶ Up p)
    [∀ p, IsFreeQuotient (offDiagonalPermLift f (p.val + 1)) (q p)]
    (π : ∀ p, Up p ⟶ X) [∀ p, Etale (π p)]
    (hπ : ∀ p, q p ≫ π p = offDiagonalToBase f (p.val + 1))
    (Vp : Fin (d + 1) → Over S) [∀ p, AlgebraicGeometry.IsAffine (Vp p).left]
    (g : ∀ p, ofOver (Vp p) ⟶ Up p) [∀ p, Etale (g p)] [∀ p, Surjective (g p)]
    (dp : Fin (d + 1) → ℕ) (hdp : ∀ p, degreesOfFibresBoundedBy (g p) (dp p))
    (F : X.Modules) [F.IsQuasicoherent] {n : ℕ}
    (hn : ∀ p : Fin (d + 1), dp p + p.val ≤ n)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})],
    IsZero (cohomology X F n))

/- Finite cohomological dimension for quasi-coherent modules. -/
#check (AlgebraicGeometry.AlgebraicSpace.exists_cohomology_isZero :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})],
    ∃ n : ℕ, ∀ (F : X.Modules) [F.IsQuasicoherent] (q : ℕ),
      n ≤ q → IsZero (cohomology X F q))
