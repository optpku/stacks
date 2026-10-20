/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.AdicSheaf
import StacksCheckRecall

/-!
# Lemma 61.28.5

On a Noetherian scheme, every constructible `Λ`-sheaf on the pro-étale site is
adic constructible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

/- Lemma 61.28.5: if `X` is a Noetherian scheme, `Λ` is a Noetherian ring, and `I ⊆ Λ` is an
ideal, then every constructible `Λ`-sheaf on `X_proétale` is adic constructible. -/
@[stacks 09BX] #check
  (AlgebraicGeometry.Scheme.ProEt.instIsAdicConstructible_of_isConstructibleLambdaSheaf :
    ∀ {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
      [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)]
      [∀ U : X.ProEt, HasWeakSheafify ((topology X).over U) (ModuleCat.{w} Λ)]
      [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
        (baseChange f).op.HasLeftKanExtension P]
      [∀ {Y : Scheme.{u}}, HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
      [∀ {Y : Scheme.{u}} (U : Y.ProEt),
        HasWeakSheafify ((topology Y).over U) (ModuleCat.{w} Λ)]
      (I : Ideal Λ) (F : Sheaf (topology X) (ModuleCat.{w} Λ))
      [IsNoetherian X] [IsConstructibleLambdaSheaf I F],
      IsAdicConstructible I F)

end AlgebraicGeometry.Scheme.ProEt
