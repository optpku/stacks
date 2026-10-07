module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import stacks_project.Chap75.Remark_75_6_3

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Lemma 86.10.1: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
quasi-compact and quasi-separated algebraic spaces over `S`. Assume `X` and `Y`
are representable, and let `f0 : X0 ⟶ Y0` be a morphism of schemes representing
`f`. Let `a` be a right adjoint of `Rf_*` from Lemma 86.3.1, and let `a0` be a
right adjoint of `Rf_*` from Duality for Schemes, Lemma 48.3.1. Then
`a0 ⋙ ofOverEpsilonStar X0` is isomorphic to `ofOverEpsilonStar Y0 ⋙ a`. -/
@[stacks 0E6E]
theorem ofOver_rightAdjoint_comm {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    [CompactSpace X0.left] [QuasiSeparatedSpace X0.left]
    [CompactSpace Y0.left] [QuasiSeparatedSpace Y0.left]
    [QuasiCompact (ofOverMap f0)] [QuasiSeparated (ofOverMap f0)]
    (a0 : Scheme.DerivedQCoh Y0.left ⥤ Scheme.DerivedQCoh X0.left)
    (a : DerivedQCoh (ofOver Y0) ⥤ DerivedQCoh (ofOver X0))
    (adj0 : Scheme.DerivedQCoh.pushforward f0.left ⊣ a0)
    (adj : pushforward (ofOverMap f0) ⊣ a) :
    IsIsomorphic (a0 ⋙ ofOverEpsilonStar X0) (ofOverEpsilonStar Y0 ⋙ a) :=
  sorry

/-- Objectwise form of the comparison of right adjoints of derived pushforward along a
representing morphism of schemes. -/
theorem ofOver_rightAdjoint_comm_app {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    [CompactSpace X0.left] [QuasiSeparatedSpace X0.left]
    [CompactSpace Y0.left] [QuasiSeparatedSpace Y0.left]
    [QuasiCompact (ofOverMap f0)] [QuasiSeparated (ofOverMap f0)]
    (a0 : Scheme.DerivedQCoh Y0.left ⥤ Scheme.DerivedQCoh X0.left)
    (a : DerivedQCoh (ofOver Y0) ⥤ DerivedQCoh (ofOver X0))
    (adj0 : Scheme.DerivedQCoh.pushforward f0.left ⊣ a0)
    (adj : pushforward (ofOverMap f0) ⊣ a)
    (K : Scheme.DerivedQCoh Y0.left) :
    IsIsomorphic ((ofOverEpsilonStar X0).obj (a0.obj K))
      (a.obj ((ofOverEpsilonStar Y0).obj K)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
