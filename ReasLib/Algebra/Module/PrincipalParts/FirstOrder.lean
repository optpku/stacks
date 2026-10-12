/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.Functorial
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The First Principal-Parts Sequence

This leaf owns the first-order principal-parts sequence of a module over a
commutative algebra.  Its maps are defined from the universal first-order
class and the universal property of Kaehler differentials; exactness is a
theorem about those canonical data.

@stack 09CN
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory KaehlerDifferential
namespace PrincipalParts.FirstOrder

section Core

variable {R S M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The universal class `m ↦ [m]` in the first principal-parts module. -/
abbrev universalClass (m : M) : PrincipalParts.module R S M 1 :=
  universalDifferential (R := R) (S := S) (M := M) 1 m

/-- The identity of an `S`-module, regarded as an `R`-linear map, has order at most one. -/
theorem id_isDifferentialOperatorOfOrder :
    (LinearMap.restrictScalars R (LinearMap.id : M →ₗ[S] M)).IsDifferentialOperatorOfOrder S 1 :=
  sorry

/-- The canonical projection from first principal parts to the original module. -/
@[stacks 09CN]
noncomputable def projection : PrincipalParts.module R S M 1 →ₗ[S] M :=
  (representingEquiv R S M 1 M).symm
    ⟨LinearMap.restrictScalars R (LinearMap.id : M →ₗ[S] M),
      id_isDifferentialOperatorOfOrder (R := R) (S := S) (M := M)⟩

/-- The first-principal-parts projection sends a universal class back to its source element. -/
@[simp]
theorem projection_apply_universalClass (m : M) :
    projection (R := R) (S := S) (M := M) (universalClass (R := R) (S := S) m) = m :=
  sorry

/-- The additive law of the derivation map associated to `m : M`. -/
theorem derivationLinear_map_add (m : M) (s₁ s₂ : S) :
    universalClass (R := R) (S := S) ((s₁ + s₂) • m) -
        (s₁ + s₂) • universalClass (R := R) (S := S) m =
      (universalClass (R := R) (S := S) (s₁ • m) -
          s₁ • universalClass (R := R) (S := S) m) +
        (universalClass (R := R) (S := S) (s₂ • m) -
          s₂ • universalClass (R := R) (S := S) m) := sorry

/-- The scalar law of the derivation map associated to `m : M`. -/
theorem derivationLinear_map_smul (m : M) (r : R) (s : S) :
    universalClass (R := R) (S := S) ((r • s) • m) -
        (r • s) • universalClass (R := R) (S := S) m =
      r • (universalClass (R := R) (S := S) (s • m) -
        s • universalClass (R := R) (S := S) m) := sorry

/-- The `R`-linear map underlying the derivation associated to `m : M`. -/
def derivationLinear (m : M) : S →ₗ[R] PrincipalParts.module R S M 1 where
  toFun s := universalClass (R := R) (S := S) (s • m) - s • universalClass (R := R) (S := S) m
  map_add' := derivationLinear_map_add (R := R) (S := S) (M := M) m
  map_smul' := derivationLinear_map_smul (R := R) (S := S) (M := M) m

/-- The derivation `s ↦ [s • m] - s • [m]` valued in first principal parts. -/
def derivation (m : M) : Derivation R S (PrincipalParts.module R S M 1) :=
  Derivation.mk' (derivationLinear (R := R) (S := S) (M := M) m) sorry

/-- The cotangent component associated to an element of the module. -/
noncomputable def cotangentComponent (m : M) :
    Ω[S⁄R] →ₗ[S] PrincipalParts.module R S M 1 :=
  (linearMapEquivDerivation R S).symm (derivation (R := R) (S := S) (M := M) m)

/-- Evaluation of a cotangent component on a universal differential. -/
theorem cotangentComponent_D (m : M) (s : S) :
    cotangentComponent (R := R) (S := S) (M := M) m (KaehlerDifferential.D R S s) =
      universalClass (R := R) (S := S) (s • m) - s • universalClass (R := R) (S := S) m :=
  sorry

/-- Additivity of the cotangent component family. -/
theorem cotangentComponent_add (m₁ m₂ : M) :
    cotangentComponent (R := R) (S := S) (M := M) (m₁ + m₂) =
      cotangentComponent (R := R) (S := S) (M := M) m₁ +
        cotangentComponent (R := R) (S := S) (M := M) m₂ := sorry

/-- Scalar compatibility of the cotangent component family. -/
theorem cotangentComponent_smul (s : S) (m : M) :
    cotangentComponent (R := R) (S := S) (M := M) (s • m) =
      s • cotangentComponent (R := R) (S := S) (M := M) m := sorry

/-- The `S`-linear family of cotangent components. -/
def cotangentLinear :
    M →ₗ[S] (Ω[S⁄R] →ₗ[S] PrincipalParts.module R S M 1) where
  toFun := cotangentComponent (R := R) (S := S) (M := M)
  map_add' := cotangentComponent_add (R := R) (S := S) (M := M)
  map_smul' := cotangentComponent_smul (R := R) (S := S) (M := M)

/-- The canonical map `Ω[S⁄R] ⊗[S] M → PrincipalParts.module R S M 1`. -/
@[stacks 09CN]
noncomputable def cotangentTo :
    TensorProduct S (Ω[S⁄R]) M →ₗ[S] PrincipalParts.module R S M 1 :=
  (TensorProduct.uncurry (RingHom.id S) M Ω[S⁄R]
      (PrincipalParts.module R S M 1)
      (cotangentLinear (R := R) (S := S) (M := M))).comp
    (TensorProduct.comm S Ω[S⁄R] M).toLinearMap

/-- The cotangent map evaluates a pure tensor using its cotangent component. -/
theorem cotangentTo_tmul (η : Ω[S⁄R]) (m : M) :
    cotangentTo (R := R) (S := S) (M := M) (η ⊗ₜ[S] m) =
      cotangentComponent (R := R) (S := S) (M := M) m η :=
  sorry

/-- The cotangent map sends `d s ⊗ m` to the first-order scalar commutator. -/
theorem cotangentTo_D_tmul (s : S) (m : M) :
    cotangentTo (R := R) (S := S) (M := M) ((KaehlerDifferential.D R S s) ⊗ₜ[S] m) =
      universalClass (R := R) (S := S) (s • m) - s • universalClass (R := R) (S := S) m :=
  sorry

/-- The projection annihilates the image of the cotangent map. -/
theorem projection_comp_cotangentTo :
    (projection (R := R) (S := S) (M := M)).comp (cotangentTo (R := R) (S := S) (M := M)) = 0 :=
  sorry

/-- The short complex
`Ω[S⁄R] ⊗[S] M ⟶ PrincipalParts.module R S M 1 ⟶ M` of first principal parts. -/
@[stacks 09CN]
noncomputable abbrev sequence : ShortComplex (ModuleCat S) :=
  ShortComplex.moduleCatMk
    (cotangentTo (R := R) (S := S) (M := M))
    (projection (R := R) (S := S) (M := M))
    (projection_comp_cotangentTo (R := R) (S := S) (M := M))

/-- The first principal-parts row is exact as a sequence of underlying functions. -/
theorem exact :
    Function.Exact (cotangentTo (R := R) (S := S) (M := M))
      (projection (R := R) (S := S) (M := M)) :=
  sorry

/-- The cotangent map into first principal parts is injective. -/
theorem cotangentTo_injective :
    Function.Injective (cotangentTo (R := R) (S := S) (M := M)) :=
  sorry

/-- The first-principal-parts projection is surjective. -/
theorem projection_surjective :
    Function.Surjective (projection (R := R) (S := S) (M := M)) :=
  sorry

/-- The first principal-parts sequence is short exact. -/
@[stacks 09CN]
theorem shortExact : (sequence (R := R) (S := S) (M := M)).ShortExact :=
  sorry

end Core

section Functoriality

variable {R S M N : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- Naturality of the first-principal-parts projection. -/
theorem projection_naturality (f : M →ₗ[S] N) :
    (projection (R := R) (S := S) (M := N)).comp
        (PrincipalParts.map (R := R) (S := S) 1 f :
          PrincipalParts.module R S M 1 →ₗ[S] PrincipalParts.module R S N 1) =
      f.comp (projection (R := R) (S := S) (M := M)) :=
  sorry

/-- Naturality of the cotangent map. -/
theorem cotangentTo_naturality (f : M →ₗ[S] N) :
    (cotangentTo (R := R) (S := S) (M := N)).comp
        (TensorProduct.map (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) f) =
      (PrincipalParts.map (R := R) (S := S) 1 f :
        PrincipalParts.module R S M 1 →ₗ[S] PrincipalParts.module R S N 1).comp
        (cotangentTo (R := R) (S := S) (M := M)) :=
  sorry

/-- Compatibility of the first two components of the induced sequence map. -/
theorem sequenceMap_comm₁₂ (f : M →ₗ[S] N) :
    ModuleCat.ofHom (TensorProduct.map (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) f) ≫
        (sequence (R := R) (S := S) (M := N)).f =
      (sequence (R := R) (S := S) (M := M)).f ≫
        ModuleCat.ofHom (PrincipalParts.map (R := R) (S := S) 1 f :
          PrincipalParts.module R S M 1 →ₗ[S] PrincipalParts.module R S N 1) := sorry

/-- Compatibility of the last two components of the induced sequence map. -/
theorem sequenceMap_comm₂₃ (f : M →ₗ[S] N) :
    ModuleCat.ofHom (PrincipalParts.map (R := R) (S := S) 1 f :
        PrincipalParts.module R S M 1 →ₗ[S] PrincipalParts.module R S N 1) ≫
        (sequence (R := R) (S := S) (M := N)).g =
      (sequence (R := R) (S := S) (M := M)).g ≫ ModuleCat.ofHom f := sorry

/-- The morphism of first principal-parts sequences induced by an `S`-linear map. -/
noncomputable def sequenceMap (f : M →ₗ[S] N) :
    sequence (R := R) (S := S) (M := M) ⟶ sequence (R := R) (S := S) (M := N) :=
  ShortComplex.Hom.mk
    (ModuleCat.ofHom (TensorProduct.map (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R]) f))
    (ModuleCat.ofHom (PrincipalParts.map (R := R) (S := S) 1 f :
      PrincipalParts.module R S M 1 →ₗ[S] PrincipalParts.module R S N 1))
    (ModuleCat.ofHom f)
    (sequenceMap_comm₁₂ (R := R) (S := S) (M := M) (N := N) f)
    (sequenceMap_comm₂₃ (R := R) (S := S) (M := M) (N := N) f)

end Functoriality

end PrincipalParts.FirstOrder
