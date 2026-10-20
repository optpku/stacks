module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.MorphismBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative

/-!
# Descent of relative flatness along inverse limits of algebraic spaces

Relative flatness of a finitely presented quasi-coherent module, and flatness of a
locally finitely presented morphism, descend from the limit of a directed inverse
system of algebraic spaces to some stage.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
variable {X0 Y0 : AlgebraicSpace S}
variable [IsQuasiCompact (D.obj i0)] [IsAbsolutelyQuasiSeparated (D.obj i0)]
variable [IsQuasiCompact X0] [IsAbsolutelyQuasiSeparated X0]
variable [IsQuasiCompact Y0] [IsAbsolutelyQuasiSeparated Y0]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- If a finitely presented quasi-coherent module becomes flat over the target after
base change to the limit of a directed inverse system, and the structure morphism is
locally of finite presentation, then the module is already flat over the stagewise
target after base change to some stage above the distinguished stage. -/
theorem exists_flatOver_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0) (F0 : X0.Modules)
    [F0.IsQuasicoherent] [F0.IsFinitePresentation]
    (h_limit : Modules.flatOver ((Modules.pullback s.limitSourceMap).obj F0) s.limitHom)
    (h_finitePresentation : AlgebraicSpace.LocallyOfFinitePresentation s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      Modules.flatOver ((Modules.pullback (s.stageSourceMap i hi0i)).obj F0)
        (s.stageHom i hi0i) := sorry

/-- If a locally finitely presented morphism of algebraic spaces becomes flat after
base change to the limit of a directed inverse system, then it becomes flat after
base change to some stage above the distinguished stage. -/
theorem exists_flat_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (h_limit : AlgebraicSpace.Flat s.limitHom)
    (h_finitePresentation : AlgebraicSpace.LocallyOfFinitePresentation s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), AlgebraicSpace.Flat (s.stageHom i hi0i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange
