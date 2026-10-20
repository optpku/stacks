/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.SheafyTrace.Coherator

/-!
# Global derived Hom trace on algebraic spaces

The canonical sheafy-trace morphism induces a comparison of global derived Homs
via the inverse Leray comparison `RΓ(X, -) ⟶ RΓ(Y, Rf_* -)` in `D(Ab)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- The inverse Leray comparison `RΓ(X, -) ⟶ RΓ(Y, Rf_* -)` in `D(Ab)`, obtained by
right-deriving the underived comparison `Γ(X, -) ⟶ Γ(Y, f_* -)`. -/
noncomputable def derivedGammaPushforwardInv {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    moduleDerivedGlobalSectionsAb X ⟶
      moduleDerivedPushforward f ⋙ moduleDerivedGlobalSectionsAb Y :=
  Functor.rightDerivedNatTrans
    (moduleDerivedGlobalSectionsAb X)
    (moduleDerivedPushforward f ⋙ moduleDerivedGlobalSectionsAb Y)
    (moduleDerivedGlobalSectionsAb.unit X) (derivedGammaPushforwardCompositeUnit f)
    (HomologicalComplex.quasiIso (Modules X) (up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex (gammaPushforwardForward f) (up ℤ))
      DerivedCategory.Q)

/-- The morphism on abelian-valued global derived Homs induced by inverse Leray
and the canonical sheafy trace for a chosen right adjunction of derived pushforward. -/
noncomputable def globalTraceMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [ModuleDerived.HasDerivedAdjunction f]
    [Functor.Monoidal (ModuleDerived.pullback f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    (moduleDerivedGlobalSectionsAb X).obj ((ihom L.obj).obj (a.obj K).obj) ⟶
      (moduleDerivedGlobalSectionsAb Y).obj
        ((ihom ((moduleDerivedPushforward f).obj L.obj)).obj K.obj) :=
  (derivedGammaPushforwardInv f).app ((ihom L.obj).obj (a.obj K).obj) ≫
    (moduleDerivedGlobalSectionsAb Y).map (sheafyTraceMap f a adj L K)

/-- The global derived Hom trace factors as inverse Leray at `RHom(L, a(K))`
followed by `RΓ(Y, -)` applied to the canonical sheafy trace. -/
theorem globalTraceMap_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [ModuleDerived.HasDerivedAdjunction f]
    [Functor.Monoidal (ModuleDerived.pullback f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    globalTraceMap f a adj L K =
      (derivedGammaPushforwardInv f).app ((ihom L.obj).obj (a.obj K).obj) ≫
        (moduleDerivedGlobalSectionsAb Y).map (sheafyTraceMap f a adj L K) :=
  sorry

/-- The canonical trace on global derived Homs is an isomorphism for
quasi-compact, quasi-separated algebraic spaces. -/
instance globalTraceMapIsIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [ModuleDerived.HasDerivedAdjunction f]
    [Functor.Monoidal (ModuleDerived.pullback f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    IsIso (globalTraceMap f a adj L K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
