/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CanonicalAlgebra
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.TensorProductBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal

/-!
# Multiplicative base change of actual Serre twists

The comparison is the fraction map of GradedMap, on the specified canonical
twisting sheaves. Its invertibility below is for tensor-product base change.
No arbitrary presentationMap or hypothesis that every twist is invertible is
used. In particular the construction applies to gradings not generated in
degree one and to nonflat changes of the coefficient ring.
-/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped TensorProduct
noncomputable section
universe u v w

namespace AlgebraicGeometry.Proj.AssociatedModule.GradedMap

section Multiplicativity
variable {R : Type v} {R' : Type w} [CommRing R] [CommRing R']
variable {A B : Type (max u v w)} [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R' B]
variable {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R' B}
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- The actual fraction map preserves the actual degree-zero unit. -/
theorem hom_map_one (ψ : 𝒜 →+*ᵍ ℬ) (hTop : projMapDomain ψ = ⊤) :
    (Scheme.Modules.pullbackUnitIso (fullMap.{u, v, w} ψ hTop)).inv ≫
      (Scheme.Modules.pullback (fullMap.{u, v, w} ψ hTop)).map
        (CanonicalAlgebra.oneHom 𝒜) ≫ hom.{u, v, w} ψ hTop 0 =
      CanonicalAlgebra.oneHom ℬ := sorry

/-- The actual fraction map preserves products in all integral degrees. -/
theorem hom_map_mul (ψ : 𝒜 →+*ᵍ ℬ) (hTop : projMapDomain ψ = ⊤) (a b : ℤ) :
    (Scheme.Modules.pullbackTensorIso (fullMap.{u, v, w} ψ hTop)
      (twistingSheaf 𝒜 a) (twistingSheaf 𝒜 b)).inv ≫
      (Scheme.Modules.pullback (fullMap.{u, v, w} ψ hTop)).map
        (CanonicalAlgebra.mulHom 𝒜 a b) ≫ hom.{u, v, w} ψ hTop (a + b) =
      (hom.{u, v, w} ψ hTop a ⊗ₘ hom.{u, v, w} ψ hTop b) ≫
        CanonicalAlgebra.mulHom ℬ a b := sorry

end Multiplicativity

section BaseChange
variable {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
variable [Algebra R R'] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The full-domain map for the actual graded tensor-product inclusion. -/
def baseChangeMap :
    Proj (tensorProductBaseChangeGrading (R' := R') 𝒜) ⟶ Proj 𝒜 :=
  fullMap.{u, u, u} (tensorProductBaseChangePsi (R' := R') 𝒜)
    (projMapDomain_tensorProductBaseChange_eq_top (R' := R') 𝒜)

/-- The base-change morphism on the specified Serre sheaves, in every integral degree. -/
def baseChangeHom (n : ℤ) :
    (Scheme.Modules.pullback (baseChangeMap (R' := R') 𝒜)).obj (twistingSheaf 𝒜 n) ⟶
      twistingSheaf (tensorProductBaseChangeGrading (R' := R') 𝒜) n :=
  hom.{u, u, u} (tensorProductBaseChangePsi (R' := R') 𝒜)
    (projMapDomain_tensorProductBaseChange_eq_top (R' := R') 𝒜) n

/-- Localization and the split graded decomposition identify this specific base-change map.
This uses no flatness and no generation-in-degree-one assumption. -/
instance baseChangeHom_isIso (n : ℤ) : IsIso (baseChangeHom (R' := R') 𝒜 n) := sorry

/-- The canonical isomorphism inverts the actual fraction-induced comparison. -/
def baseChangeIso (n : ℤ) :
    (Scheme.Modules.pullback (baseChangeMap (R' := R') 𝒜)).obj (twistingSheaf 𝒜 n) ≅
      twistingSheaf (tensorProductBaseChangeGrading (R' := R') 𝒜) n :=
  asIso (baseChangeHom (R' := R') 𝒜 n)

/-- The base-change comparison preserves the canonical degree-zero unit. -/
theorem baseChangeHom_map_one :
    (Scheme.Modules.pullbackUnitIso (baseChangeMap (R' := R') 𝒜)).inv ≫
      (Scheme.Modules.pullback (baseChangeMap (R' := R') 𝒜)).map
        (CanonicalAlgebra.oneHom 𝒜) ≫ baseChangeHom (R' := R') 𝒜 0 =
      CanonicalAlgebra.oneHom (tensorProductBaseChangeGrading (R' := R') 𝒜) :=
  hom_map_one.{u, u, u} (tensorProductBaseChangePsi (R' := R') 𝒜)
    (projMapDomain_tensorProductBaseChange_eq_top (R' := R') 𝒜)

/-- The base-change comparison preserves the canonical products in every integral degree. -/
theorem baseChangeHom_map_mul (a b : ℤ) :
    (Scheme.Modules.pullbackTensorIso (baseChangeMap (R' := R') 𝒜)
      (twistingSheaf 𝒜 a) (twistingSheaf 𝒜 b)).inv ≫
      (Scheme.Modules.pullback (baseChangeMap (R' := R') 𝒜)).map
        (CanonicalAlgebra.mulHom 𝒜 a b) ≫ baseChangeHom (R' := R') 𝒜 (a + b) =
      (baseChangeHom (R' := R') 𝒜 a ⊗ₘ baseChangeHom (R' := R') 𝒜 b) ≫
        CanonicalAlgebra.mulHom (tensorProductBaseChangeGrading (R' := R') 𝒜) a b :=
  hom_map_mul.{u, u, u} (tensorProductBaseChangePsi (R' := R') 𝒜)
    (projMapDomain_tensorProductBaseChange_eq_top (R' := R') 𝒜) a b

end BaseChange
end AlgebraicGeometry.Proj.AssociatedModule.GradedMap
