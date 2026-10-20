/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleCohomology
import StacksCheckRecall

/-!
# Lemma 61.19.4

On an affine scheme, the pro-étale cohomology of `ε⁻¹ I` vanishes in positive
degrees when `I` is an injective abelian sheaf on the small étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

/- Lemma 61.19.4: if `X` is an affine scheme and `I` is an injective abelian sheaf
on `X.Etale`, then `H^p(X.ProEt, ε⁻¹ I) = 0` for all `p > 0`. -/
@[stacks 099U] #check
  (AlgebraicGeometry.Scheme.etaleToProEtPullback_injective_isZero_cohomology :
    ∀ (X : Scheme.{u}) [IsAffine X]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}, (etaleToProEt X).op.HasLeftKanExtension F]
    [HasSheafify (ProEt.topology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (ProEt.topology X) AddCommGrpCat.{u})]
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
    {p : ℕ} (hp : 0 < p),
    IsZero (((etaleToProEtPullback X AddCommGrpCat.{u}).obj I).H' p (ProEt.mk (𝟙 X))))
