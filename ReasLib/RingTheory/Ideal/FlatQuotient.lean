module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Order.Minimal
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.LinearAlgebra.QuotientByIdeal.Mapped
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat quotients by ideals

For an ideal `J`, `IsFlatQuotient J M` records flatness of the canonical quotient module
`M ⧸ J • ⊤` over `R ⧸ J`.  The quotient scalar action, intersection criterion, Artinian least
ideal, and base-change universal property live together here so later chapters can import one
small owner instead of rebuilding the predicate and its instances.

@stack 0522
@stack 0524
@stack 0525
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Ideal

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The canonical `(R ⧸ J)`-module structure on `M ⧸ J • ⊤`, exposed under the ideal owner
namespace without introducing a second global instance. -/
@[stacks 0522 "flat quotient module structure"]
abbrev quotientSmulTopModule (J : Ideal R) :
    Module (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))) :=
  Module.instQuotientIdealSubmoduleHSMulTop M J

/-- The quotient scalar action is compatible with the ambient `R`-action.  This named instance
is the self-map specialization used by quotient base-change constructions. -/
@[stacks 0522 "flat quotient scalar tower"]
instance quotientSmulTopTower (J : Ideal R) :
    IsScalarTower R (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))) :=
  Module.IsTorsionBySet.isScalarTower
    (Module.isTorsionBySet_quotient_ideal_smul M J)

/-- `Ideal.IsFlatQuotient`: the quotient `M ⧸ J • ⊤` is flat over `R ⧸ J`. -/
@[stacks 0522 "flat quotient ideal predicate"]
abbrev IsFlatQuotient (J : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  Module.Flat (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M)))

/-- Stacks `0522`: flat quotient ideals are closed under binary intersections. -/
@[stacks 0522 "flat quotient ideals are closed under intersections"]
theorem IsFlatQuotient.inf {I J : Ideal R}
    (hI : I.IsFlatQuotient M) (hJ : J.IsFlatQuotient M) :
    (I ⊓ J).IsFlatQuotient M := sorry

/-- The top ideal always gives a flat quotient. -/
@[stacks 0524 "top ideal has flat quotient"]
theorem top_isFlatQuotient : (⊤ : Ideal R).IsFlatQuotient M := sorry

/-- Stacks `0524`: an Artinian ring has a least ideal with flat quotient. -/
@[stacks 0524 "least ideal with flat quotient over an Artinian ring"]
theorem exists_isLeastFlatQuotient [IsArtinianRing R] :
    ∃ I : Ideal R, IsLeast {J : Ideal R | J.IsFlatQuotient M} I := sorry

variable {R' : Type w} [CommRing R'] [Algebra R R']
variable [IsArtinianRing R]

/-- Stacks `0525`: the least flat-quotient ideal is characterized by base-change flatness. -/
@[stacks 0525 "flat base change detects the least flat-quotient ideal"]
theorem flat_baseChange_iff_map_eq_bot {I : Ideal R}
    (hI : IsLeast {J : Ideal R | J.IsFlatQuotient M} I) :
    Module.Flat R' (R' ⊗[R] M) ↔ I.map (algebraMap R R') = ⊥ := sorry

end Ideal
