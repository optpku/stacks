/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Affine functors of points over a base scheme

This file packages the `Γ ⊣ Spec` adjunction as a reusable equivalence for morphisms in
`Over (Spec R)`.
-/

@[expose] public section

open Opposite CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Scheme morphisms from `X` to `Spec(R)` are equivalent to ring homomorphisms from `R` to
the global sections of `X`. -/
@[stacks 01I1 "scheme Gamma-Spec hom equivalence"]
noncomputable def homToSpecGlobalSectionsEquiv (X : Scheme.{u}) (R : CommRingCat.{u}) :
    (X ⟶ Spec R) ≃ (R ⟶ Γ(X, ⊤)) :=
  (ΓSpec.adjunction.homEquiv X (op R)).symm.trans (CategoryTheory.opEquiv _ _)

/-- The forward map of `homToSpecGlobalSectionsEquiv` is pullback on global sections. -/
@[simp, stacks 01I1 "Gamma-Spec equivalence forward formula"]
theorem homToSpecGlobalSectionsEquiv_apply
    (X : Scheme.{u}) (R : CommRingCat.{u}) (f : X ⟶ Spec R) :
    homToSpecGlobalSectionsEquiv X R f = (Scheme.ΓSpecIso R).inv ≫ f.appTop := sorry

/-- The inverse map is the canonical morphism to `Spec` followed by the spectrum map. -/
@[simp, stacks 01I1 "Gamma-Spec equivalence inverse formula"]
theorem homToSpecGlobalSectionsEquiv_symm_apply
    (X : Scheme.{u}) (R : CommRingCat.{u}) (φ : R ⟶ Γ(X, ⊤)) :
    (homToSpecGlobalSectionsEquiv X R).symm φ = X.toSpecΓ ≫ Spec.map φ := sorry

namespace OverSpec

/-- The affine scheme `Spec(A)` over `Spec(R)` induced contravariantly by `φ : R ⟶ A`. -/
@[stacks 01I1 "affine object over a spectrum"]
noncomputable abbrev affine {R A : CommRingCat.{u}} (φ : R ⟶ A) : Over (Spec R) :=
  Over.mk (Spec.map φ)

/-- The ring homomorphism `R ⟶ Γ(T, ⊤)` encoded by `T : Over (Spec R)`. -/
@[stacks 01I1 "base map on global sections"]
noncomputable def baseRingHom {R : CommRingCat.{u}} (T : Over (Spec R)) :
    R ⟶ Γ(T.left, ⊤) :=
  homToSpecGlobalSectionsEquiv T.left R T.hom

/-- A coordinate-ring homomorphism compatible with the two maps from the base ring. -/
@[stacks 01I1 "base-compatible coordinate-ring map"]
abbrev CompatibleRingHom {R A : CommRingCat.{u}} (φ : R ⟶ A) (T : Over (Spec R)) :=
  Under.mk φ ⟶ Under.mk (baseRingHom T)

/-- The global-sections map induced by an over-morphism is compatible with the base maps. -/
@[stacks 01I1 "global-sections map respects the base"]
theorem ringHomOfHom_comp {R A : CommRingCat.{u}} (φ : R ⟶ A)
    {T : Over (Spec R)} (f : T ⟶ affine φ) :
    φ ≫ homToSpecGlobalSectionsEquiv T.left A f.left = baseRingHom T := sorry

/-- The base-compatible global-sections homomorphism induced by an over-morphism. -/
@[stacks 01I1 "coordinate-ring map of an over-morphism"]
noncomputable def ringHomOfHom {R A : CommRingCat.{u}} (φ : R ⟶ A)
    {T : Over (Spec R)} (f : T ⟶ affine φ) : CompatibleRingHom φ T :=
  Under.homMk (homToSpecGlobalSectionsEquiv T.left A f.left) (ringHomOfHom_comp φ f)

/-- The underlying ring map of `ringHomOfHom` is the pullback on global sections. -/
@[simp, stacks 01I1 "underlying coordinate-ring map"]
theorem ringHomOfHom_right {R A : CommRingCat.{u}} (φ : R ⟶ A)
    {T : Over (Spec R)} (f : T ⟶ affine φ) :
    (ringHomOfHom φ f).right = homToSpecGlobalSectionsEquiv T.left A f.left := sorry

/-- A compatible ring map gives a scheme morphism whose composite to the base is `T.hom`. -/
@[stacks 01I1 "classified affine morphism respects the base"]
theorem homOfRingHom_w {R A : CommRingCat.{u}} (φ : R ⟶ A)
    {T : Over (Spec R)} (ψ : CompatibleRingHom φ T) :
    (homToSpecGlobalSectionsEquiv T.left A).symm ψ.right ≫ Spec.map φ = T.hom := sorry

/-- The over-morphism determined by a base-compatible coordinate-ring homomorphism. -/
@[stacks 01I1 "affine over-morphism of a coordinate-ring map"]
noncomputable def homOfRingHom {R A : CommRingCat.{u}} (φ : R ⟶ A)
    {T : Over (Spec R)} (ψ : CompatibleRingHom φ T) : T ⟶ affine φ :=
  Over.homMk ((homToSpecGlobalSectionsEquiv T.left A).symm ψ.right) (homOfRingHom_w φ ψ)

/-- The underlying scheme morphism of `homOfRingHom` is classified by its ring map. -/
@[simp, stacks 01I1 "underlying classified scheme morphism"]
theorem homOfRingHom_left {R A : CommRingCat.{u}} (φ : R ⟶ A)
    {T : Over (Spec R)} (ψ : CompatibleRingHom φ T) :
    (homOfRingHom φ ψ).left =
      (homToSpecGlobalSectionsEquiv T.left A).symm ψ.right := sorry

/-- Reconstructing an over-morphism from its global-sections map is the identity. -/
@[stacks 01I1 "affine classification left inverse"]
theorem homOfRingHom_ringHomOfHom {R A : CommRingCat.{u}} (φ : R ⟶ A)
    {T : Over (Spec R)} (f : T ⟶ affine φ) :
    homOfRingHom φ (ringHomOfHom φ f) = f := sorry

/-- Extracting global sections from the over-morphism defined by a compatible map is the
identity. -/
@[stacks 01I1 "affine classification right inverse"]
theorem ringHomOfHom_homOfRingHom {R A : CommRingCat.{u}} (φ : R ⟶ A)
    {T : Over (Spec R)} (ψ : CompatibleRingHom φ T) :
    ringHomOfHom φ (homOfRingHom φ ψ) = ψ := sorry

/-- Morphisms over `Spec(R)` into an affine scheme are canonically equivalent to compatible
coordinate-ring homomorphisms. -/
@[stacks 01I1 "affine functor of points over a base"]
noncomputable def homEquiv {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (T : Over (Spec R)) : (T ⟶ affine φ) ≃ CompatibleRingHom φ T where
  toFun := ringHomOfHom φ
  invFun := homOfRingHom φ
  left_inv := homOfRingHom_ringHomOfHom φ
  right_inv := ringHomOfHom_homOfRingHom φ

end OverSpec
end AlgebraicGeometry.Scheme

