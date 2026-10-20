/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Representable
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Derived pushforward for represented algebraic spaces

The canonical étale-to-Zariski equivalence on derived quasi-coherent categories
commutes with derived pushforward along quasi-compact, quasi-separated morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Exact inverse image from the Zariski site to the étale site of a represented
algebraic space is an equivalence on derived quasi-coherent categories. -/
instance schemeToSpaceDerived_isEquivalence {S : Scheme.{u}} (U : Over S) :
    (schemeToSpaceDerived U).IsEquivalence :=
  (schemeRestrictionEquivalence U).isEquivalence_functor

/-- The canonical étale-to-Zariski equivalences commute naturally with derived
pushforward along a quasi-compact, quasi-separated morphism represented by schemes. -/
theorem ofOver_pushforward_comm {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    [QuasiCompact (ofOverMap f0)] [QuasiSeparated (ofOverMap f0)] :
    IsIsomorphic
      (Scheme.DerivedQCoh.pushforwardCohomologyIn f0.left ⋙ schemeToSpaceDerived Y0)
      (schemeToSpaceDerived X0 ⋙ pushforwardCohomologyIn (ofOverMap f0)) :=
  sorry

/-- Right adjoints of derived pushforward along a representing morphism of schemes
commute naturally with the canonical scheme-to-space derived equivalences. -/
theorem ofOver_rightAdjoint_comm {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    [CompactSpace X0.left] [QuasiSeparatedSpace X0.left]
    [CompactSpace Y0.left] [QuasiSeparatedSpace Y0.left]
    [QuasiCompact (ofOverMap f0)] [QuasiSeparated (ofOverMap f0)]
    (a0 : Scheme.DerivedQCoh Y0.left ⥤ Scheme.DerivedQCoh X0.left)
    (a : DerivedQCoh (ofOver Y0) ⥤ DerivedQCoh (ofOver X0))
    (adj0 : Scheme.DerivedQCoh.pushforwardCohomologyIn f0.left ⊣ a0)
    (adj : pushforwardCohomologyIn (ofOverMap f0) ⊣ a) :
    IsIsomorphic (a0 ⋙ schemeToSpaceDerived X0) (schemeToSpaceDerived Y0 ⋙ a) :=
  sorry

/-- At each derived quasi-coherent object, right adjoints of derived pushforward
along a representing morphism of schemes agree up to isomorphism under the
canonical scheme-to-space derived equivalences. -/
theorem ofOver_rightAdjoint_comm_app {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    [CompactSpace X0.left] [QuasiSeparatedSpace X0.left]
    [CompactSpace Y0.left] [QuasiSeparatedSpace Y0.left]
    [QuasiCompact (ofOverMap f0)] [QuasiSeparated (ofOverMap f0)]
    (a0 : Scheme.DerivedQCoh Y0.left ⥤ Scheme.DerivedQCoh X0.left)
    (a : DerivedQCoh (ofOver Y0) ⥤ DerivedQCoh (ofOver X0))
    (adj0 : Scheme.DerivedQCoh.pushforwardCohomologyIn f0.left ⊣ a0)
    (adj : pushforwardCohomologyIn (ofOverMap f0) ⊣ a)
    (K : Scheme.DerivedQCoh Y0.left) :
    IsIsomorphic ((schemeToSpaceDerived X0).obj (a0.obj K))
      (a.obj ((schemeToSpaceDerived Y0).obj K)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
