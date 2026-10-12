/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

variable (R : Type u) [CommRing R]
variable (X : AlgebraicSpace (Spec (CommRingCat.of R)))
variable (ℱ 𝒢 : X.Modules) [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] (u : ℱ ⟶ 𝒢)
variable (hG_flat : Modules.flatOver 𝒢 (toBase X))

/- Situation 77.8.1: `S = Spec (CommRingCat.of R)` is an affine scheme, `X` is an
algebraic space over `S`, `u : ℱ ⟶ 𝒢` is a map of quasi-coherent 𝒪_X-modules, and
`𝒢` is flat over `S`. -/
@[stacks 0CWA] #check (Spec (CommRingCat.of R) : Scheme.{u})
@[stacks 0CWA] #check (inferInstance : IsAffine (Spec (CommRingCat.of R)))
@[stacks 0CWA] #check (X : AlgebraicSpace (Spec (CommRingCat.of R)))
@[stacks 0CWA] #check (ℱ : X.Modules)
@[stacks 0CWA] #check (𝒢 : X.Modules)
@[stacks 0CWA] #check (inferInstance : ℱ.IsQuasicoherent)
@[stacks 0CWA] #check (inferInstance : 𝒢.IsQuasicoherent)
@[stacks 0CWA] #check (u : ℱ ⟶ 𝒢)
@[stacks 0CWA] #check (toBase X : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
@[stacks 0CWA] #check (hG_flat : Modules.flatOver 𝒢 (toBase X))
