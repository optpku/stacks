/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_8_10_Instances
public import stacks_project.Chap75.Lemma_75_10_5_Gamma
public import stacks_project.Chap86.«86_3_2_1_Trace»

/-!
# Global derived Hom trace on algebraic spaces

The sheafy-trace morphism induces a comparison of global derived Homs after
identifying `RΓ(X, -)` with `RΓ(Y, Rf_* -)` in `D(Ab)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Inverse-Leray identification `RΓ(X, -) ⟶ RΓ(Y, Rf_* -)` in `D(Ab)`, obtained by
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

/-- The morphism on abelian-valued derived global sections induced by inverse Leray
and the sheafy-trace map. -/
noncomputable def globalTraceMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [Functor.LaxMonoidal (moduleDerivedPushforward f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    (moduleDerivedGlobalSectionsAb X).obj ((ihom L.obj).obj (a.obj K).obj) ⟶
      (moduleDerivedGlobalSectionsAb Y).obj
        ((ihom ((moduleDerivedPushforward f).obj L.obj)).obj K.obj) :=
  (derivedGammaPushforwardInv f).app ((ihom L.obj).obj (a.obj K).obj) ≫
    (moduleDerivedGlobalSectionsAb Y).map (sheafyTrace f a adj L K)

/-- `globalTraceMap` is inverse Leray at `RHom(L, a(K))` followed by `RΓ(Y, -)` of
`sheafyTrace`. -/
theorem globalTraceMap_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [Functor.LaxMonoidal (moduleDerivedPushforward f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    globalTraceMap f a adj L K =
      (derivedGammaPushforwardInv f).app ((ihom L.obj).obj (a.obj K).obj) ≫
        (moduleDerivedGlobalSectionsAb Y).map (sheafyTrace f a adj L K) :=
  sorry

/-- The induced map on global derived Homs is an isomorphism. -/
instance globalTraceMapIsIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [Functor.LaxMonoidal (moduleDerivedPushforward f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    IsIso (globalTraceMap f a adj L K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

