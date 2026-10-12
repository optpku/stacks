/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {D : OrderDual I ⥤ Scheme.{u}} {i0 : I} {X0 Y0 : Scheme.{u}}
variable [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
variable [CompactSpace X0] [QuasiSeparatedSpace X0]
variable [CompactSpace Y0] [QuasiSeparatedSpace Y0]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/-- If a locally finitely presented morphism becomes finite locally free after base change to
the limit of a directed inverse system, then it becomes finite locally free after base change
to some stage above the distinguished stage. -/
theorem exists_isFiniteLocallyFree_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (h_limit : IsFiniteLocallyFree s.limitHom)
    (h_finitePresentation : LocallyOfFinitePresentation s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), IsFiniteLocallyFree (s.stageHom i hi0i) := sorry

/-- If a locally finitely presented morphism becomes finite locally free of rank `d` after base
change to the limit of a directed inverse system, then it becomes finite locally free of rank
`d` after base change to some stage above the distinguished stage. -/
theorem exists_isFiniteLocallyFreeOfRank_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0) (d : ℕ)
    (h_limit : IsFiniteLocallyFreeOfRank s.limitHom d)
    (h_finitePresentation : LocallyOfFinitePresentation s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), IsFiniteLocallyFreeOfRank (s.stageHom i hi0i) d := sorry

end AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange
