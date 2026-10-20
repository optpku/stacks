module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.SheafyTrace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RightAdjoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Permanence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Permanence

/-!
# Coherated sheafy trace on algebraic spaces

Applying the quasicoherent coherator, the right adjoint of `inclusion Y`,
to the canonical sheafy trace yields an isomorphism in `DerivedQCoh Y`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The canonical sheafy-trace morphism after applying the quasicoherent coherator. -/
noncomputable def coheratedSheafyTraceMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [ModuleDerived.HasDerivedAdjunction f]
    [Functor.Monoidal (ModuleDerived.pullback f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    (inclusion Y).rightAdjoint.obj
        ((moduleDerivedPushforward f).obj ((ihom L.obj).obj (a.obj K).obj)) ⟶
      (inclusion Y).rightAdjoint.obj
        ((ihom ((moduleDerivedPushforward f).obj L.obj)).obj K.obj) :=
  (inclusion Y).rightAdjoint.map (sheafyTraceMap f a adj L K)

/-- Applying the right adjoint of `inclusion Y` to `sheafyTraceMap` recovers
`coheratedSheafyTraceMap`. -/
theorem coheratedSheafyTraceMap_eq_map {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [ModuleDerived.HasDerivedAdjunction f]
    [Functor.Monoidal (ModuleDerived.pullback f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    coheratedSheafyTraceMap f a adj L K =
      (inclusion Y).rightAdjoint.map (sheafyTraceMap f a adj L K) :=
  rfl

/-- The coherated sheafy-trace morphism is the right adjoint of `inclusion Y`
applied to the adjunction-induced internal-Hom comparison of `Rf_*` followed by
the included counit. -/
theorem coheratedSheafyTraceMap_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [ModuleDerived.HasDerivedAdjunction f]
    [Functor.Monoidal (ModuleDerived.pullback f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    coheratedSheafyTraceMap f a adj L K =
      (inclusion Y).rightAdjoint.map
        (@InternalHom.comparison _ _ _ _ _ _ (moduleDerivedPushforward f)
            (moduleDerivedPushforward.laxMonoidal f) L.obj (a.obj K).obj _ _ ≫
          (ihom ((moduleDerivedPushforward f).obj L.obj)).map
            ((pushforwardCohomologyIn.inclusionIso f).inv.app (a.obj K) ≫
              (inclusion Y).map (adj.counit.app K))) :=
  rfl

/-- The coherated sheafy-trace morphism is an isomorphism in `DerivedQCoh Y`. -/
instance coheratedSheafyTraceMapIsIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [ModuleDerived.HasDerivedAdjunction f]
    [Functor.Monoidal (ModuleDerived.pullback f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    IsIso (coheratedSheafyTraceMap f a adj L K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
