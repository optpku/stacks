/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.ComparisonData
import StacksCheckRecall

/-!
# Lemma 25.6.5 compatibility

The source spectral sequence is the terminal-presheaf specialization of the functorial
presheaf-target system.  Its second page remains the canonical hypercovering Cech cohomology,
while the shared terminal-cohomology bridge identifies its abutment with global cohomology.
-/

noncomputable section

universe w v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasExt.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]

/- Lemma 25.6.5 [stacks 09VY], existence clause: the terminal presheaf has a functorial
hypercovering spectral-sequence system under the source's finite-limit hypotheses. -/
@[stacks 09VY "existence"] #check
  HypercoveringOf.Cech.spectralSequenceSystem_nonempty.{w, v, u}
    (J := J) (Presheaf.terminal C)

variable
  (S : HypercoveringOf.Cech.SpectralSequenceSystem.{w, v, u}
    (J := J) (Presheaf.terminal C))
  (K : HypercoveringOf.Terminal.{w} J)
  (ℱ : Sheaf J AddCommGrpCat.{max w v})

/- Lemma 25.6.5 [stacks 09VY], second-page clause:
`E₂^{p,q} ≅ Ȟ^p(K, U ↦ H^q(U, ℱ))`. -/
@[stacks 09VY "second page"] #check S.pageTwoIso K ℱ

/- Lemma 25.6.5 [stacks 09VY], convergence clause: the spectral sequence abuts to the global
cohomology groups `H^n(ℱ)`. -/
@[stacks 09VY "global abutment"] #check S.abutsGlobal K ℱ

#check @GrothendieckTopology.freeAbelianTerminalIsoInteger
#check @Sheaf.TerminalCohomology.isoExt
#check @Sheaf.TerminalCohomology.isomorphicGlobal

end CategoryTheory
