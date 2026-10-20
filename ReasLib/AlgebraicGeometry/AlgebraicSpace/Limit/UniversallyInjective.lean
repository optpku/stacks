/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.MorphismBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
variable {X0 Y0 : AlgebraicSpace S}
variable [IsQuasiCompact (D.obj i0)] [IsAbsolutelyQuasiSeparated (D.obj i0)]
variable [IsQuasiCompact X0] [IsAbsolutelyQuasiSeparated X0]
variable [IsQuasiCompact Y0] [IsAbsolutelyQuasiSeparated Y0]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- For a directed inverse system with affine transition morphisms, suppose the
distinguished stage and the source and target of a morphism over it are
quasi-compact and absolutely quasi-separated. If the morphism is locally of
finite type and becomes universally injective after base change to the limit,
then it becomes universally injective after base change to some stage above
the distinguished stage. -/
theorem exists_universallyInjective_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (h_limit : AlgebraicSpace.UniversallyInjective s.limitHom)
    (h_finiteType : AlgebraicSpace.LocallyOfFiniteType s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      AlgebraicSpace.UniversallyInjective (s.stageHom i hi0i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange
