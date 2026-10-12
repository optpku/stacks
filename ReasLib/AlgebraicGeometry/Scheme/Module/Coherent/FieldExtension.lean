/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent

/-!
# Coherent modules under field extension

This leaf records coherence of a pulled-back coherent module on a proper scheme over a field.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.FieldExtension

/-- Pullback along a field extension preserves coherence for coherent modules on schemes proper
over the base field. -/
instance baseChange_isCoherent
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    (Scheme.Modules.FieldExtension.baseChange k K f ℱ).IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules.FieldExtension
