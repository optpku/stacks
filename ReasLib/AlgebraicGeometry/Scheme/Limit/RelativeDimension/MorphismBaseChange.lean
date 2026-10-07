module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.MorphismBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Limit.RelativeDimension

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

/-- If a locally finite-type morphism has relative dimension at most `d` after base change to
the limit of a directed inverse system, then it has relative dimension at most `d` after base
change to some stage above the distinguished stage. -/
theorem exists_relativeDimensionLE_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0) (d : ℕ)
    (h_limit : Scheme.Hom.RelativeDimensionLE s.limitHom d)
    (h_finiteType : LocallyOfFiniteType s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      Scheme.Hom.RelativeDimensionLE (s.stageHom i hi0i) d := sorry

/-- If a locally finitely presented morphism has relative dimension `d` after base change to
the limit of a directed inverse system, then it has relative dimension `d` after base change to
some stage above the distinguished stage. -/
theorem exists_relativeDimension_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0) (d : ℕ)
    (h_limit : Scheme.Hom.RelativeDimension s.limitHom d)
    (h_finitePresentation : LocallyOfFinitePresentation s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      Scheme.Hom.RelativeDimension (s.stageHom i hi0i) d := sorry

end AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange
