/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SmallRelocalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u

/- Lemma 66.27.2: the scheme-localization conjugate of the small étale morphism
is two-isomorphic to localization at the sheaf parameter of the commutative square. -/
@[stacks 04M5] #check (AlgebraicGeometry.AlgebraicSpace.etaleRelocalizeIso :
  ∀ {S : Scheme.{u}} {U V : Over S} {X Y : AlgebraicSpace S}
    (p : ofOver U ⟶ X) (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y)
    [Etale p] [Etale q] (hcomm : p ≫ f = g ≫ q),
    @RingedSite.ToposHom.TwoIso
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
      (etaleRelocalizeConjugateScheme p g q)
      (Relocalization.parameterRingedHom p g f q hcomm))
