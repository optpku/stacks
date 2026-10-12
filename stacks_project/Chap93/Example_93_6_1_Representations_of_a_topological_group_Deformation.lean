/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ContinuousRepresentation

/-!
# Compatibility surface for deformation categories of representations

The residue representation and its deformation category are owned by
`ContinuousRep`; this file keeps a direct typed import surface for chapter
consumers.
-/

@[expose] public section

open CategoryTheory

universe u

variable (Γ Λ k : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]

variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/- The residue representation constructor. -/
#check (ContinuousRep.ofResidue Γ Λ k :
  (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) →
    ContinuousRep.IsContinuousDiscrete ρ0 → ContinuousRep Γ Λ k)

/- The deformation category is an Over category. -/
#check (ContinuousRep.deformationCategory Γ Λ k :
  (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) →
    ContinuousRep.IsContinuousDiscrete ρ0 → Type (u + 1))

end
