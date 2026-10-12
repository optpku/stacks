/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.VirtualNormalBundle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Dual

/-!
# Pullback of virtual normal bundles

This file constructs the virtual normal bundle induced by a cartesian square of immersions.
The underlying module is ordinary scheme-module pullback, and its quotient map is the composite
of dual pullback, the pulled original quotient, and conormal base change.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- The quotient map on a pulled virtual normal bundle: first identify the new dual with the
pullback of the old dual, then pull back the old quotient and apply conormal base change. -/
noncomputable def pullbackMap {Z X Z' X' : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {f : X' ⟶ X}
    [IsImmersion i'] [IsImmersion i] (sq : IsPullback g i' i f)
    (V : VirtualNormalBundle i) :
    Scheme.Modules.dual ((Scheme.Modules.pullback g).obj V.module) ⟶
      conormalSheaf i' :=
  (Scheme.Modules.pullbackDualIso g V.module V.isFiniteLocallyFree).inv ≫
    (Scheme.Modules.pullback g).map V.map ≫ Conormal.map sq.toCommSq

/-- The quotient map on the pulled virtual normal bundle is an epimorphism. -/
theorem pullbackMap_epi {Z X Z' X' : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {f : X' ⟶ X}
    [IsImmersion i'] [IsImmersion i] (sq : IsPullback g i' i f)
    (V : VirtualNormalBundle i) : Epi (pullbackMap sq V) := sorry

/-- Pull a virtual normal bundle back through a cartesian square of immersions. -/
noncomputable def pullback {Z X Z' X' : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {f : X' ⟶ X}
    [IsImmersion i'] [IsImmersion i] (sq : IsPullback g i' i f)
    (V : VirtualNormalBundle i) : VirtualNormalBundle i' where
  module := (Scheme.Modules.pullback g).obj V.module
  isFiniteLocallyFree :=
    @Scheme.Modules.pullback_isFiniteLocallyFree _ _ g V.module V.isFiniteLocallyFree
  map := pullbackMap sq V
  map_epi := pullbackMap_epi sq V

/-- The module of a pulled virtual normal bundle is the ordinary pullback of the original
module. -/
theorem pullback_module {Z X Z' X' : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {f : X' ⟶ X}
    [IsImmersion i'] [IsImmersion i] (sq : IsPullback g i' i f)
    (V : VirtualNormalBundle i) :
    (pullback sq V).module = (Scheme.Modules.pullback g).obj V.module := sorry

/-- The quotient map of a pulled virtual normal bundle is the explicit pullback map. -/
theorem pullback_map {Z X Z' X' : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {f : X' ⟶ X}
    [IsImmersion i'] [IsImmersion i] (sq : IsPullback g i' i f)
    (V : VirtualNormalBundle i) :
    (pullback sq V).map = pullbackMap sq V := sorry

/-- The pulled module is finite locally free and its explicit map to the new conormal sheaf is
an epimorphism. -/
theorem pullback_spec {Z X Z' X' : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {f : X' ⟶ X}
    [IsImmersion i'] [IsImmersion i] (sq : IsPullback g i' i f)
    (V : VirtualNormalBundle i) :
    Scheme.Modules.IsFiniteLocallyFree ((Scheme.Modules.pullback g).obj V.module) ∧
      Epi (pullbackMap sq V) := sorry

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
