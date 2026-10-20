/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.TopologyComparison
import StacksCheckRecall

/-!
# Lemma 96.11.4

Quasi-coherence of a module presheaf on a category fibred in groupoids may be
tested on the associated Zariski, étale, or fppf ringed site.
-/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver

universe u

/- Lemma 96.11.4: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in groupoids.
Let `F` be a presheaf of modules on `𝒳`. The following are equivalent: `F` is an
object of `Mod(𝒳_Zar, 𝒪_𝒳)` and quasi-coherent on `(𝒳_Zar, 𝒪_𝒳)` in the sense of
Modules on Sites, Definition 18.23.1; `F` is an object of `Mod(𝒳_étale, 𝒪_𝒳)`
and quasi-coherent on `(𝒳_étale, 𝒪_𝒳)` in the sense of Modules on Sites,
Definition 18.23.1; and `F` is a quasi-coherent module on `𝒳` in the sense of
Definition 96.11.1. -/
@[stacks 0EM8] #check
  (AlgebraicGeometry.GroupoidsOver.isQuasicoherentOn_zariski_iff_etale_iff_fppf :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
      (F : PresheafOfModules.{u} (structureSheaf X).obj),
      List.TFAE [isQuasicoherentOn F .zariski, isQuasicoherentOn F .etale,
        isQuasicoherentOn F .fppf])
