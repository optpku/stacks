/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import stacks_project.Chap76.Lemma_76_26_3_CohenMacaulay
public import stacks_project.Chap76.Lemma_76_29_3_ReducedFiberLocus
public import stacks_project.Chap99.Situation_99_15_1_Category

/-!
# Geometrically reduced curves are Cohen–Macaulay

The geometrically reduced locus of the stack of curves is contained in the
Cohen–Macaulay locus. Both loci are packaged as object properties of families
of curves, matching the open substacks 𝒞urves^{geomred} and 𝒞urves^{CM}.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.Scheme
namespace CohenMacaulay

/-- A reduced locally Noetherian scheme of topological Krull dimension at most `1` is
Cohen–Macaulay. -/
theorem of_isReduced_of_topologicalKrullDim_le_one
    (X : Scheme.{u}) [IsReduced X] [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) :
    Scheme.CohenMacaulay X := sorry

end CohenMacaulay
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The object property of families of curves whose fibres are geometrically reduced,
corresponding to the open substack 𝒞urves^{geomred}. -/
def geometricallyReduced (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ ∀ y : Points (ofOver (base P)), y ∈ geometricallyReducedFiberLocus (hom P)

/-- Membership in `geometricallyReduced` means every fibre of the structure morphism is
geometrically reduced. -/
theorem geometricallyReduced_iff {S : Scheme.{u}} (P : Obj S) :
    geometricallyReduced S P ↔
      ∀ y : Points (ofOver (base P)), y ∈ geometricallyReducedFiberLocus (hom P) :=
  sorry

/-- The object property of Cohen–Macaulay families of curves, corresponding to the
open substack 𝒞urves^{CM}. -/
def cohenMacaulay (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ CohenMacaulay (hom P)

/-- Membership in `cohenMacaulay` is Cohen–Macaulayness of the structure morphism. -/
theorem cohenMacaulay_iff {S : Scheme.{u}} (P : Obj S) :
    cohenMacaulay S P ↔ CohenMacaulay (hom P) :=
  sorry

/-- Lemma 109.10.2: we have 𝒞urves^{geomred} ⊂ 𝒞urves^{CM} as open substacks of 𝒞urves. -/
@[stacks 0E1G]
theorem geometricallyReduced_le_cohenMacaulay (S : Scheme.{u}) :
    geometricallyReduced S ≤ cohenMacaulay S :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
