/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Stable
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.SchemeOverField
open Scheme.DerivedQCoh.ProperDualizingComplex
open SheafOfModules
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 109.22.3: a proper scheme of dimension at most one over a field is a stable
curve if and only if it is at-worst-nodal of dimension one, has constant global
functions, and has ample canonical dualizing module. -/
@[stacks 0E76] #check (AlgebraicGeometry.SchemeOverField.isStableCurve_iff_curveDualizingModule_isAmple :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1),
    isStableCurve X ↔
      atWorstNodal X ∧ topologicalKrullDim X.left = 1 ∧
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) ∧
        Scheme.Modules.isAmpleObject (curveDualizingModule X.hom))

#check (AlgebraicGeometry.SchemeOverField.isStableCurve_iff :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1),
    isStableCurve X ↔
      atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          2 ≤ genus X hdim1 hΓ ∧
            ¬ Nonempty (RationalTail X) ∧ ¬ Nonempty (RationalBridge X))

#check (AlgebraicGeometry.Scheme.Hom.stableOpen_eq_top_iff :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom)),
    f.stableOpen h_unit = ⊤ ↔
      ∀ s : S, isStableCurve (Over.mk (f.fiberToSpecResidueField s)))

#check (AlgebraicGeometry.Scheme.Hom.factorsThrough_stableOpen_iff :
  ∀ {X S T : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom))
    (g : T ⟶ S),
    (∃ lift : T ⟶ (f.stableOpen h_unit).toScheme,
      lift ≫ (f.stableOpen h_unit).ι = g) ↔
      ∀ t : T, isStableCurve (Over.mk ((pullback.snd f g).fiberToSpecResidueField t)))
