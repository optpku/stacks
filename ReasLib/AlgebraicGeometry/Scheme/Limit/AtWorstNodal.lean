/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.MorphismBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Syntomic.MorphismBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Limit.RelativeDimension.MorphismBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Unramified
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal

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

/-- At-worst-nodality of a locally finitely presented morphism descends from the
limit of a directed inverse system with affine transition morphisms to some stage. -/
theorem exists_atWorstNodal_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (h_limit : AtWorstNodal s.limitHom)
    (h_finitePresentation : LocallyOfFinitePresentation s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), AtWorstNodal (s.stageHom i hi0i) := sorry

end AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange
