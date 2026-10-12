/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap104.Definition_104_5_1_LQCohFbc

/-!
# Fppf descent for locally quasi-coherent modules with flat base change

The Proposition 103.8.1 (1) declaration is shared here so its use does not
import the conflicting projection owners in the full proposition module.
The underlying module presheaf is unchanged; this is a sheaf law, not a
choice of a module or an inverse morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Proposition 103.8.1 (1): an étale module in `LQCoh^{fbc}(𝒪_X)` is a sheaf
for the fppf topology, hence an object of `Mod(𝒪_X)`. -/
@[stacks 0771]
theorem isSheaf_fppf_of_lqcohFbc {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F] [HasFlatBaseChange F] :
    Presheaf.IsSheaf (fppfRingedSite X).siteTopology
      (etaleModulePresheaf F).presheaf := sorry

end AlgebraicGeometry.GroupoidsOver
