module

public import stacks_project.Chap67.Lemma_67_8_10_Instances
public import stacks_project.Chap75.Lemma_75_19_1_Instances
public import stacks_project.Chap86.«86_3_2_1_Trace»

/-!
# Coherated sheafy trace on algebraic spaces

Applying the right adjoint of `inclusion Y` (the functor `DQ_Y` of
Derived Categories of Spaces, Section 75.19) to the sheafy-trace morphism
`sheafyTrace` yields a morphism in `DerivedQCoh Y`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The sheafy-trace morphism after applying the right adjoint of `inclusion Y`. -/
noncomputable def coheratedSheafyTraceMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [Functor.LaxMonoidal (moduleDerivedPushforward f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    (inclusion Y).rightAdjoint.obj
        ((moduleDerivedPushforward f).obj ((ihom L.obj).obj (a.obj K).obj)) ⟶
      (inclusion Y).rightAdjoint.obj
        ((ihom ((moduleDerivedPushforward f).obj L.obj)).obj K.obj) :=
  (inclusion Y).rightAdjoint.map (sheafyTrace f a adj L K)

/-- Applying the right adjoint of `inclusion Y` to `sheafyTrace` recovers
`coheratedSheafyTraceMap`. -/
theorem coheratedSheafyTraceMap_eq_map {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [Functor.LaxMonoidal (moduleDerivedPushforward f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    coheratedSheafyTraceMap f a adj L K =
      (inclusion Y).rightAdjoint.map (sheafyTrace f a adj L K) :=
  sorry

/-- The coherated sheafy-trace morphism is the right adjoint of `inclusion Y`
applied to the internal-Hom comparison of `Rf_*` followed by the included counit. -/
theorem coheratedSheafyTraceMap_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [Functor.LaxMonoidal (moduleDerivedPushforward f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    coheratedSheafyTraceMap f a adj L K =
      (inclusion Y).rightAdjoint.map
        (InternalHom.comparison (moduleDerivedPushforward f) L.obj (a.obj K).obj ≫
          (ihom ((moduleDerivedPushforward f).obj L.obj)).map
            ((pushforwardCohomologyIn.inclusionIso f).inv.app (a.obj K) ≫
              (inclusion Y).map (adj.counit.app K))) :=
  sorry

/-- The coherated sheafy-trace morphism is an isomorphism in `DerivedQCoh Y`. -/
instance coheratedSheafyTraceMapIsIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [Functor.LaxMonoidal (moduleDerivedPushforward f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    IsIso (coheratedSheafyTraceMap f a adj L K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
