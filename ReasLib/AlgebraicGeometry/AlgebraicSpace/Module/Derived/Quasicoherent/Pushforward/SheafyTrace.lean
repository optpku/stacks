module

public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward.Monoidal

/-!
# Sheafy trace for derived pushforward on algebraic spaces

The morphism `Rf_* RHom(L, a(K)) ⟶ RHom(Rf_* L, K)` is the
internal-Hom comparison of `Rf_*` followed by `RHom(Rf_* L, ε_K)` for
the counit `ε` of a chosen adjunction `Rf_* ⊣ a` on `DerivedQCoh`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For the supplied lax monoidal structure on derived pushforward, the sheafy-trace morphism
`Rf_* RHom(L, a(K)) ⟶ RHom(Rf_* L, K)` in `D(𝒪_Y)`. -/
noncomputable def sheafyTrace {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [Functor.LaxMonoidal (moduleDerivedPushforward f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    (moduleDerivedPushforward f).obj ((ihom L.obj).obj (a.obj K).obj) ⟶
      (ihom ((moduleDerivedPushforward f).obj L.obj)).obj K.obj :=
  InternalHom.comparison (moduleDerivedPushforward f) L.obj (a.obj K).obj ≫
    (ihom ((moduleDerivedPushforward f).obj L.obj)).map
      ((pushforwardCohomologyIn.inclusionIso f).inv.app (a.obj K) ≫
        (inclusion Y).map (adj.counit.app K))

/-- The sheafy-trace morphism is the internal-Hom comparison of `Rf_*` followed by
the included counit of the chosen derived pushforward adjunction. -/
theorem sheafyTrace_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [Functor.LaxMonoidal (moduleDerivedPushforward f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    sheafyTrace f a adj L K =
      InternalHom.comparison (moduleDerivedPushforward f) L.obj (a.obj K).obj ≫
        (ihom ((moduleDerivedPushforward f).obj L.obj)).map
          ((pushforwardCohomologyIn.inclusionIso f).inv.app (a.obj K) ≫
            (inclusion Y).map (adj.counit.app K)) :=
  rfl

/-- The sheafy-trace morphism formed with the lax monoidal structure induced by
the derived module pullback–pushforward adjunction. -/
noncomputable def sheafyTraceMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [ModuleDerived.HasDerivedAdjunction f]
    [Functor.Monoidal (ModuleDerived.pullback f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    (moduleDerivedPushforward f).obj ((ihom L.obj).obj (a.obj K).obj) ⟶
      (ihom ((moduleDerivedPushforward f).obj L.obj)).obj K.obj :=
  @InternalHom.comparison _ _ _ _ _ _ (moduleDerivedPushforward f)
      (moduleDerivedPushforward.laxMonoidal f) L.obj (a.obj K).obj _ _ ≫
    (ihom ((moduleDerivedPushforward f).obj L.obj)).map
      ((pushforwardCohomologyIn.inclusionIso f).inv.app (a.obj K) ≫
        (inclusion Y).map (adj.counit.app K))

/-- The distinguished sheafy trace is the adjunction-induced internal-Hom comparison
followed by postcomposition with the included quasicoherent adjunction counit. -/
theorem sheafyTraceMap_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [ModuleDerived.HasDerivedAdjunction f]
    [Functor.Monoidal (ModuleDerived.pullback f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    sheafyTraceMap f a adj L K =
      @InternalHom.comparison _ _ _ _ _ _ (moduleDerivedPushforward f)
          (moduleDerivedPushforward.laxMonoidal f) L.obj (a.obj K).obj _ _ ≫
        (ihom ((moduleDerivedPushforward f).obj L.obj)).map
          ((pushforwardCohomologyIn.inclusionIso f).inv.app (a.obj K) ≫
            (inclusion Y).map (adj.counit.app K)) := rfl

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
