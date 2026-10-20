/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Relocalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 66.27.1: transporting the spaces-étale ringed-topos morphism through étale
localization identifies it with localization at the induced pullback arrow. -/
@[stacks 04M4] #check (AlgebraicGeometry.AlgebraicSpace.spacesEtaleRelocalizeIso :
  ∀ {S : Scheme.{u}} {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y)
    [Etale p] [Etale q] (hcomm : p ≫ f = g ≫ q),
    @RingedSite.ToposHom.TwoIso
      ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
      ((spacesRingedSite Y).localization (spacesEtaleSite.mk q)) _ _
      (spacesEtaleRelocalizeConjugate p g f q hcomm)
      (spacesRingedHom.localizationAt f (spacesEtaleSite.mk q)
        (spacesEtalePullbackLift p g f q hcomm)))
