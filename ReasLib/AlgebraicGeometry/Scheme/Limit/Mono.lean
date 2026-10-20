module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Isomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Diagonal

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

/-- If a morphism becomes a monomorphism after base change to the limit of a directed inverse
system and is locally of finite type, then it becomes a monomorphism after base change to some
stage above the distinguished stage. -/
theorem exists_mono_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0) (h_limit : Mono s.limitHom)
    (h_finiteType : LocallyOfFiniteType s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), Mono (s.stageHom i hi0i) := sorry

end AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange
