/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Lemma_52_25_2
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.TripleEulerCharacteristic

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.CoherentTriple

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {S : CoherentTripleSetup A}

/-- The intrinsic Euler characteristic of a coherent triple, obtained from any admissible
comparison. -/
noncomputable def eulerCharacteristic (T : CoherentTriple S) : ℤ :=
  @AlgebraicGeometry.Scheme.Modules.CoherentTriple.eulerCharacteristic A _ _ _
    S.f S.f_mem_maximalIdeal T.F T.F₀ T.coherent_F T.coherent_F₀ T.mul_f_injective T.α

end AlgebraicGeometry.CoherentTriple
