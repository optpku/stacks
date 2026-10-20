module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.MorphismBaseChange

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

/-- If a locally finitely presented morphism becomes an isomorphism after base change to the
limit of a directed inverse system, then it becomes an isomorphism after base change to some
stage above the distinguished stage. -/
theorem exists_isIso_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0) (h_limit : IsIso s.limitHom)
    (h_finitePresentation : LocallyOfFinitePresentation s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), IsIso (s.stageHom i hi0i) := sorry

end AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange
