/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Quasicoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver

universe u

/- Lemma 96.12.2: a module presheaf is quasi-coherent if and only if it is locally
quasi-coherent and all canonical small-étale comparison morphisms are isomorphisms. -/
@[stacks 06WK] #check
  (AlgebraicGeometry.GroupoidsOver.isQuasicoherentOn_fppf_iff_isLocallyQuasicoherent :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
      (F : PresheafOfModules.{u} (structureSheaf X).obj),
      isQuasicoherentOn F .fppf ↔
        ∃ hF : IsLocallyQuasicoherent F,
          ∀ {x y : X.total} (φ : x ⟶ y),
            IsIso (moduleComparison φ (etaleModuleOfPresheaf F hF.isEtaleSheaf)))
