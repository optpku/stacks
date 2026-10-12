/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.InverseSystem
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

/-!
# Derived module systems on a formal completion

This module bundles compatible pseudo-coherent derived modules on the base-change
stages of a scheme over the limit of a sequential inverse system of rings.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.FormalCompletion

/-- A compatible system of pseudo-coherent derived modules on the base-change
stages of a scheme over the limit of a sequential inverse system of rings. -/
structure System
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (X : Scheme.{u}) (f : X ⟶ Spec A_lim.cone.pt)
    (Xn : ℕ → Scheme.{u}) (p : ∀ n, Xn n ⟶ X)
    (q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n)))
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom (i n).toShHom)] where
  /-- Every successor transition of the ring system is surjective. -/
  surjective : A.Surjective
  /-- Every successor transition of the ring system has locally nilpotent kernel. -/
  kernelLocallyNilpotent : A.KernelLocallyNilpotent
  /-- Each stage is the base change of the ambient scheme to the corresponding ring. -/
  isPullback : ∀ n,
    IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f
  /-- Each stage maps to the ambient scheme by a closed immersion. -/
  isClosedImmersion : ∀ n, IsClosedImmersion (p n)
  /-- Successor maps of stages commute with the maps to the ambient scheme. -/
  comp_p : ∀ n, i n ≫ p (n + 1) = p n
  /-- Successor maps of stages commute with the maps to the rings in the inverse system. -/
  comp_q : ∀ n,
    i n ≫ q (n + 1) = q n ≫ Spec.map (A.stepMap n)
  /-- The derived module at each base-change stage. -/
  K : ∀ n, RingedSpace.ModuleDerived (Xn n).toRingedSpace
  /-- Every derived module in the system is pseudo-coherent. -/
  isPseudoCoherent : ∀ n, RingedSpace.ModuleDerived.IsPseudoCoherent (K n)
  /-- The successor transition, written as a map to derived pushforward. -/
  φ : ∀ n, K (n + 1) ⟶
    (RingedSpace.moduleDerivedPushforward (i n).toShHom).obj (K n)
  /-- The derived-pullback map adjoint to every successor transition is an isomorphism. -/
  pullbackTransition_isIso : ∀ n, IsIso
    (((RingedSpace.modulePullbackDerivedPushforwardAdjunction (i n).toShHom).homEquiv
      (K (n + 1)) (K n)).symm (φ n))

namespace System

variable {A : SequentialInverseSystem CommRingCat.{u}} {A_lim : LimitCone A}
variable {X : Scheme.{u}} {f : X ⟶ Spec A_lim.cone.pt}
variable {Xn : ℕ → Scheme.{u}} {p : ∀ n, Xn n ⟶ X}
variable {q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n))}
variable {i : ∀ n, Xn n ⟶ Xn (n + 1)}
variable [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
variable [∀ n, HasPair (RingedSpace.opensRingedSiteHom (i n).toShHom)]

/-- Construct a formal-completion system from its geometric stages, derived modules,
successor maps, and their compatibility properties. -/
noncomputable def of
    (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f)
    (h_closed : ∀ n, IsClosedImmersion (p n))
    (hiX : ∀ n, i n ≫ p (n + 1) = p n)
    (hiA : ∀ n,
      i n ≫ q (n + 1) = q n ≫ Spec.map (A.stepMap n))
    (K : ∀ n, RingedSpace.ModuleDerived (Xn n).toRingedSpace)
    (hK : ∀ n, RingedSpace.ModuleDerived.IsPseudoCoherent (K n))
    (φ : ∀ n, K (n + 1) ⟶
      (RingedSpace.moduleDerivedPushforward (i n).toShHom).obj (K n))
    (hφ : ∀ n, IsIso
      (((RingedSpace.modulePullbackDerivedPushforwardAdjunction (i n).toShHom).homEquiv
        (K (n + 1)) (K n)).symm (φ n))) :
    System A A_lim X f Xn p q i where
  surjective := h_surjective
  kernelLocallyNilpotent := h_kernel
  isPullback := h_pullback
  isClosedImmersion := h_closed
  comp_p := hiX
  comp_q := hiA
  K := K
  isPseudoCoherent := hK
  φ := φ
  pullbackTransition_isIso := hφ

/-- The derived-pullback transition adjoint to the pushforward-form successor map. -/
noncomputable def pullbackTransition (S : System A A_lim X f Xn p q i) (n : ℕ) :
    (RingedSpace.modulePullbackDerived (i n).toShHom).obj (S.K (n + 1)) ⟶ S.K n :=
  ((RingedSpace.modulePullbackDerivedPushforwardAdjunction (i n).toShHom).homEquiv
    (S.K (n + 1)) (S.K n)).symm (S.φ n)

/-- The constructed formal-completion system has the supplied derived modules and
transitions, and satisfies all the supplied geometric and compatibility conditions. -/
theorem of_spec
    (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f)
    (h_closed : ∀ n, IsClosedImmersion (p n))
    (hiX : ∀ n, i n ≫ p (n + 1) = p n)
    (hiA : ∀ n,
      i n ≫ q (n + 1) = q n ≫ Spec.map (A.stepMap n))
    (K : ∀ n, RingedSpace.ModuleDerived (Xn n).toRingedSpace)
    (hK : ∀ n, RingedSpace.ModuleDerived.IsPseudoCoherent (K n))
    (φ : ∀ n, K (n + 1) ⟶
      (RingedSpace.moduleDerivedPushforward (i n).toShHom).obj (K n))
    (hφ : ∀ n, IsIso
      (((RingedSpace.modulePullbackDerivedPushforwardAdjunction (i n).toShHom).homEquiv
        (K (n + 1)) (K n)).symm (φ n))) :
    (of h_surjective h_kernel h_pullback h_closed hiX hiA K hK φ hφ).K = K ∧
      (of h_surjective h_kernel h_pullback h_closed hiX hiA K hK φ hφ).φ = φ ∧
      A.Surjective ∧ A.KernelLocallyNilpotent ∧
      (∀ n, IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f) ∧
      (∀ n, IsClosedImmersion (p n)) ∧
      (∀ n, i n ≫ p (n + 1) = p n) ∧
      (∀ n, i n ≫ q (n + 1) = q n ≫ Spec.map (A.stepMap n)) ∧
      (∀ n, RingedSpace.ModuleDerived.IsPseudoCoherent (K n)) ∧
      (∀ n, IsIso
        ((of h_surjective h_kernel h_pullback h_closed hiX hiA K hK φ hφ).pullbackTransition n)) := sorry

end System

end AlgebraicGeometry.Scheme.ModuleDerived.FormalCompletion
