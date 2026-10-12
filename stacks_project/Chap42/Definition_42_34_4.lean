/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowCohomology.FirstChern

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 42.34.4: For `X` locally of finite type over the universally catenary
dimensioned base `(S, δ)` and an invertible `𝒪_X`-module `ℒ`, the first Chern class
`firstChernClass δ p ℒ : ChowCohomology.degree δ p 1` is the bivariant class constructed
in Lemma 42.34.3. -/
@[stacks 0FDW] #check (@AlgebraicGeometry.ChowCohomology.firstChernClass :
  ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ],
    AlgebraicGeometry.ChowCohomology.degree δ p 1)
