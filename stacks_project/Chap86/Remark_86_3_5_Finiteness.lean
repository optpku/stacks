module

public import stacks_project.Chap86.Lemma_86_3_3_SheafyTrace
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap86.Lemma_86_3_2_BoundedBelow

/-!
# Finiteness criteria for the sheafy-trace morphism

If both derived internal Hom objects in the sheafy-trace comparison have
quasi-coherent cohomology, or if `L` and `Rf_* L` are perfect, or if `K` is
bounded below and `L` and `Rf_* L` are pseudo-coherent, then `sheafyTrace` is
an isomorphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- If the derived internal Hom of `L` into `a.obj K` on `X` and the derived internal
Hom of `Rf_* L` into `K` on `Y` both have quasi-coherent cohomology, then
`sheafyTrace` is an isomorphism. -/
theorem sheafyTrace_isIso_of_derivedQCoh {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [Functor.LaxMonoidal (moduleDerivedPushforward f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y)
    (h_source : derivedQuasiCoherentModuleProperty X
      ((ihom L.obj).obj (a.obj K).obj))
    (h_target : derivedQuasiCoherentModuleProperty Y
      ((ihom ((moduleDerivedPushforward f).obj L.obj)).obj K.obj)) :
    IsIso (sheafyTrace f a adj L K) :=
  sorry

/-- If `L` and its derived pushforward `Rf_* L` are perfect, then `sheafyTrace` is an
isomorphism. -/
theorem sheafyTrace_isIso_of_isPerfect {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [Functor.LaxMonoidal (moduleDerivedPushforward f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y)
    (hL : ModuleDerived.IsPerfect L.obj)
    (hRfL : ModuleDerived.IsPerfect ((moduleDerivedPushforward f).obj L.obj)) :
    IsIso (sheafyTrace f a adj L K) :=
  sorry

/-- If `K` is bounded below and `L` and its derived pushforward `Rf_* L` are
pseudo-coherent, then `sheafyTrace` is an isomorphism. -/
theorem sheafyTrace_isIso_of_isPseudoCoherent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
    [Functor.LaxMonoidal (moduleDerivedPushforward f)]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y)
    (hK : K.obj.IsBoundedBelow) (hL : IsPseudoCoherent X L.obj)
    (hRfL : IsPseudoCoherent Y ((moduleDerivedPushforward f).obj L.obj)) :
    IsIso (sheafyTrace f a adj L K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
