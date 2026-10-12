/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ContinuousRepresentation

/-!
# Compatibility surface for the continuous representation category

The reusable category is owned by `ContinuousRep`; this file keeps a direct
typed import surface for chapter consumers.
-/

@[expose] public section

open CategoryTheory

universe u

variable (Γ Λ k : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]

/- The bundled representation owner. -/
#check (ContinuousRep Γ Λ k : Type (u + 1))

/- The projection is cofibered in groupoids. -/
#check (ContinuousRep.instIsCofiberedInGroupoids Γ Λ k :
  Functor.IsFibered.InGroupoids (ContinuousRep.forget Γ Λ k).op)

end
