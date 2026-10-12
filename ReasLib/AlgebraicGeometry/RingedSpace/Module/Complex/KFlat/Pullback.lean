/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.KFlat.EnoughPoints
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
public import Mathlib.Topology.Sheaves.Points
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of K-flat complexes on ringed spaces

The opens-site presentation has enough points, so the generic ringed-site pullback criterion gives
the ringed-space statement without exposing stalk comparisons or auxiliary monoidal instances.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex.IsKFlat

variable {X Y : RingedSpace.{u}}

/-- Lemma 20.26.8 (06YC): pullback along a morphism of ringed spaces preserves K-flat complexes.
The public interface contains only the morphism, the complex, and its K-flatness hypothesis. -/
@[stacks 06YC "pullback preserves K-flat complexes"]
theorem pullback (f : X ⟶ Y) {K : CochainComplex (Modules Y) ℤ}
    (hK : K.IsKFlat) :
    (((f^*).mapHomologicalComplex (up ℤ)).obj K).IsKFlat := sorry

end AlgebraicGeometry.RingedSpace.CochainComplex.IsKFlat

end
