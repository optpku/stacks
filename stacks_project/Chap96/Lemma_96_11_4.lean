/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap96.Lemma_96_11_4_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 96.11.4

Quasi-coherence of a module presheaf on a category fibred in groupoids may be
tested on the associated Zariski, étale, or fppf ringed site.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)
variable (F : PresheafOfModules.{u} (structureSheaf X).obj)

/-- Lemma 96.11.4: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in groupoids.
Let `F` be a presheaf of modules on `𝒳`. The following are equivalent: `F` is an
object of `Mod(𝒳_Zar, 𝒪_𝒳)` and quasi-coherent on `(𝒳_Zar, 𝒪_𝒳)` in the sense of
Modules on Sites, Definition 18.23.1; `F` is an object of `Mod(𝒳_étale, 𝒪_𝒳)`
and quasi-coherent on `(𝒳_étale, 𝒪_𝒳)` in the sense of Modules on Sites,
Definition 18.23.1; and `F` is a quasi-coherent module on `𝒳` in the sense of
Definition 96.11.1. -/
@[stacks 0EM8]
theorem isQuasicoherentOn_zariski_iff_etale_iff_fppf :
    List.TFAE [isQuasicoherentOn F .zariski, isQuasicoherentOn F .etale,
      isQuasicoherentOn F .fppf] :=
  sorry

/-- Quasi-coherence on the associated Zariski site is equivalent to
quasi-coherence on the associated étale site. -/
theorem isQuasicoherentOn_zariski_iff_etale :
    isQuasicoherentOn F .zariski ↔ isQuasicoherentOn F .etale :=
  sorry

/-- Quasi-coherence on the associated étale site is equivalent to
quasi-coherence on the associated fppf site. -/
theorem isQuasicoherentOn_etale_iff_fppf :
    isQuasicoherentOn F .etale ↔ isQuasicoherentOn F .fppf :=
  sorry

/-- Quasi-coherence on the associated Zariski site is equivalent to
quasi-coherence on the associated fppf site. -/
theorem isQuasicoherentOn_zariski_iff_fppf :
    isQuasicoherentOn F .zariski ↔ isQuasicoherentOn F .fppf :=
  sorry

end AlgebraicGeometry.GroupoidsOver
