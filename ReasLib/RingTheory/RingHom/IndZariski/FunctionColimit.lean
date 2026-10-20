/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndZariski
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.DiscreteQuotient
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

universe u v w x

open DiscreteQuotient
open CategoryTheory Limits

namespace RingHom.IndZariski

/-- Precomposition of function rings along a map of index types. -/
def functionRingMap {k : Type u} [CommRing k] {X : Type v} {Y : Type w} (φ : Y → X) :
    (X → k) →+* (Y → k) :=
  RingHom.pi fun y ↦ Pi.evalRingHom (fun _ ↦ k) (φ y)

/-- Evaluating a precomposition map at a point recovers ordinary composition. -/
theorem functionRingMap_apply {k : Type u} [CommRing k] {X : Type v} {Y : Type w}
    (φ : Y → X) (g : X → k) (y : Y) :
    functionRingMap φ g y = g (φ y) :=
  sorry

/-- The underlying point-set of a discrete quotient, used as a function-ring domain. -/
abbrev pointType {T : Type v} [TopologicalSpace T] (S : DiscreteQuotient T) : Type v :=
  S

/-- Precomposition along a comparison of discrete quotients gives the transition
map in the opposite-order diagram of function rings. -/
def functionRingMap_ofLE (k : Type u) [CommRing k] {T : Type v} [TopologicalSpace T]
    {S₁ S₂ : (DiscreteQuotient T)ᵒᵈ} (h : S₁ ≤ S₂) :
    (pointType (OrderDual.ofDual S₁) → k) →+* (pointType (OrderDual.ofDual S₂) → k) :=
  functionRingMap (ofLE (OrderDual.ofDual_le_ofDual.mpr h))

/-- The function-ring transitions on opposite discrete quotients form a directed system. -/
instance instDirectedSystem_functionRingMap (k : Type u) [CommRing k]
    (T : Type v) [TopologicalSpace T] :
    DirectedSystem (fun S : (DiscreteQuotient T)ᵒᵈ ↦ (pointType (OrderDual.ofDual S) → k))
      (fun _ _ h ↦ functionRingMap_ofLE k h) :=
  sorry

/-- The filtered colimit of the function rings on the discrete quotients of a space.
These quotients are finite when the space is compact. -/
noncomputable abbrev functionColimit (k : Type u) [CommRing k] (T : Type v)
    [TopologicalSpace T] : Type (max u v) :=
  Ring.DirectLimit (fun S : (DiscreteQuotient T)ᵒᵈ ↦ (pointType (OrderDual.ofDual S) → k))
    (fun _ _ h ↦ functionRingMap_ofLE k h)

namespace functionColimit

/-- The canonical map from the function ring on a discrete quotient into the colimit. -/
noncomputable abbrev of (k : Type u) [CommRing k] (T : Type v) [TopologicalSpace T]
    (S : DiscreteQuotient T) :
    (S → k) →+* functionColimit k T :=
  Ring.DirectLimit.of (fun S : (DiscreteQuotient T)ᵒᵈ ↦ (pointType (OrderDual.ofDual S) → k))
    (fun _ _ h ↦ functionRingMap_ofLE k h) (OrderDual.toDual S)

/-- A continuous map to a finite Hausdorff space induces a map from its function ring
into the function-ring colimit of the domain. -/
noncomputable def ofFinite (k : Type u) [CommRing k]
    {T : Type v} [TopologicalSpace T] {S : Type w}
    [TopologicalSpace S] [T2Space S] [_root_.Finite S] (p : C(T, S)) :
    (S → k) →+* functionColimit k T :=
  let pLC : LocallyConstant T S :=
    ⟨p, (IsLocallyConstant.iff_continuous p).mpr p.continuous⟩
  (of k T pLC.discreteQuotient).comp (functionRingMap pLC.lift)

/-- Finite-stage maps commute with precomposition along continuous maps of finite
Hausdorff spaces. -/
theorem ofFinite_comp {k : Type u} [CommRing k]
    {T : Type v} [TopologicalSpace T] {S : Type w}
    [TopologicalSpace S] [T2Space S] [_root_.Finite S]
    {R : Type x} [TopologicalSpace R] [T2Space R] [_root_.Finite R]
    (p : C(T, S)) (q : C(S, R)) :
    (ofFinite k p).comp (functionRingMap q) = ofFinite k (q.comp p) := sorry

end functionColimit

/-- The structure map from the coefficient ring to the function-ring colimit. -/
noncomputable def algebraMap_functionColimit (k : Type u) [CommRing k] (T : Type v)
    [TopologicalSpace T] :
    k →+* functionColimit k T :=
  (functionColimit.of k T ⊤).comp (Pi.constRingHom (⊤ : DiscreteQuotient T) k)

/-- The canonical algebra structure on the function-ring colimit. -/
noncomputable instance instAlgebra_functionColimit (k : Type u) [CommRing k]
    (T : Type v) [TopologicalSpace T] :
    Algebra k (functionColimit k T) :=
  RingHom.toAlgebra (algebraMap_functionColimit k T)

/-- The structure map factors through the constant-functions map of every quotient stage. -/
theorem algebraMap_functionColimit_comp_of {k : Type u} [CommRing k]
    {T : Type v} [TopologicalSpace T] (S : DiscreteQuotient T) :
    (functionColimit.of k T S).comp (Pi.constRingHom S k) =
      algebraMap_functionColimit k T :=
  sorry

namespace functionColimit

/-- Every finite-stage map sends constant functions along the canonical coefficient map. -/
theorem ofFinite_const {k : Type u} [CommRing k]
    {T : Type v} [TopologicalSpace T] {S : Type w}
    [TopologicalSpace S] [T2Space S] [_root_.Finite S] (p : C(T, S)) :
    (ofFinite k p).comp (Pi.constRingHom S k) = algebraMap_functionColimit k T := sorry

/-- For a limiting cone of a small cofiltered diagram of finite profinite spaces,
every compatible family of ring maps from the stage function rings descends uniquely
to the function-ring colimit of the cone point. -/
theorem existsUnique_desc_of_isLimit (k : Type u) [Field k]
    {J : Type w} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ Profinite.{v}) [∀ j, _root_.Finite (F.obj j)]
    (c : Cone F) (hc : IsLimit c) (B : Type x) [CommRing B]
    (g : ∀ j, (F.obj j → k) →+* B)
    (h_compat : ∀ {i j : J} (a : i ⟶ j),
      (g i).comp (functionRingMap (F.map a)) = g j) :
    ∃! desc : functionColimit k c.pt →+* B,
      ∀ j, desc.comp (ofFinite k (c.π.app j).hom.hom) = g j := sorry

end functionColimit

/-- For a field and a profinite space, the function-ring colimit is ind-Zariski
over the field and its prime spectrum is homeomorphic to the given space. -/
theorem functionColimit_spec
    {k : Type u} [Field k] {T : Type v}
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] :
    (algebraMap_functionColimit k T).IndZariski ∧
      Nonempty (PrimeSpectrum (functionColimit k T) ≃ₜ T) :=
  sorry

end RingHom.IndZariski
