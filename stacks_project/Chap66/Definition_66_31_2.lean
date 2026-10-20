/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Lemma_66_31_1
public import stacks_project.Chap66.Lemma_66_31_3_LocallyProjective
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Definition 66.31.2: let `S` be a scheme, let `X` be an algebraic space over `S`,
and let `F` be a quasi-coherent `𝒪_X`-module. We say `F` is locally projective if
the equivalent conditions of Lemma 66.31.1 are satisfied. -/
@[stacks 060R]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsLocallyProjective :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, X.Modules → Prop)

#check (existsSurjectiveEtale_iff_forallEtale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent],
    existsSurjectiveEtale F ↔ forallEtale F)

#check (isLocallyProjective_iff_exists_surjective_etale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent],
    IsLocallyProjective F ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X) (hφ : Etale φ),
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ ∧
          IsLocallyProjective (restrictEtale F φ hφ))

#check (isLocallyProjective_iff_forall_etale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent],
    IsLocallyProjective F ↔
      ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ],
        IsLocallyProjective (restrict F φ))
