/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Definition_71_10_3_MeromorphicSection

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite
open PresheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Definition 71.10.3 (1)
Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `ℱ` be a sheaf of `𝒪_X`-modules
on `X_étale`. We denote `𝒦_X(ℱ)` the sheaf of `𝒦_X`-modules which is the sheafification of the
presheaf `U ↦ 𝒮(U)⁻¹ ℱ(U)`. Equivalently `𝒦_X(ℱ) = ℱ ⊗_{𝒪_X} 𝒦_X`. -/
@[stacks 0EN5]
theorem meromorphicSectionSheaf_spec {S : Scheme.{u}} (X : AlgebraicSpace S)
    (F : X.Modules) :
    meromorphicSectionSheaf X F =
      (moduleSheafification (smallEtaleTopology X)
          (regularStructureSections X).localizationPresheaf).obj
        (meromorphicSectionPresheaf X F) :=
  sorry

/-- Definition 71.10.3 (2)
A meromorphic section of `ℱ` is a global section of `𝒦_X(ℱ)`. -/
@[stacks 0EN5]
theorem meromorphicSections_spec {S : Scheme.{u}} (X : AlgebraicSpace S)
    (F : X.Modules) :
    meromorphicSections X F = (meromorphicSectionSheaf X F).sections :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
