/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.MorphismBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange

/-- If the limit base change of a morphism is quasi-finite and the original morphism is locally
of finite type, then its base change is quasi-finite at some stage above the distinguished
stage. -/
theorem exists_quasiFinite_stage_of_limitHom
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {D : OrderDual I ⥤ Scheme.{u}} {i0 : I} {X0 Y0 : Scheme.{u}}
    [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
    [CompactSpace X0] [QuasiSeparatedSpace X0]
    [CompactSpace Y0] [QuasiSeparatedSpace Y0]
    [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (h_limit : Scheme.Hom.QuasiFinite s.limitHom)
    (h_finiteType : LocallyOfFiniteType s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), Scheme.Hom.QuasiFinite (s.stageHom i hi0i) := sorry

end AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange
