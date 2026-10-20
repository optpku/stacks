/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Spectrum
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.GroupAction
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf

/-!
# Field-valued points of free group quotients

Finite Galois equivariant lifts describe field-valued points of the fppf
quotient sheaf of a residue-field-free group action.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FieldExtension

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- Equivariance of `φ : Spec(k') ⟶ U` for a subgroup `H ≤ G` identified with
`Gal(k'/k)`: the left action of `e h` on `Spec(k')` is `FieldExtension.Galois.baseAut k k' ((e h)⁻¹)`,
and this intertwines with `ρ h`. -/
def IsGalEquivariant {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {H : Subgroup G} (e : H ≃* Gal(k'/k))
    {σ : Spec (CommRingCat.of k) ⟶ S} (φ : specExtend σ k' ⟶ U) : Prop :=
  ∀ h : H, FieldExtension.Galois.baseAut k k' ((e h)⁻¹) ≫ φ.left = φ.left ≫ (ρ (h : G)).hom.left

/-- Unfolding of `IsGalEquivariant` as the scheme-level intertwining identity. -/
theorem isGalEquivariant_iff {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {H : Subgroup G} (e : H ≃* Gal(k'/k))
    {σ : Spec (CommRingCat.of k) ⟶ S} (φ : specExtend σ k' ⟶ U) :
    IsGalEquivariant ρ e φ ↔
      ∀ h : H, FieldExtension.Galois.baseAut k k' ((e h)⁻¹) ≫ φ.left = φ.left ≫ (ρ (h : G)).hom.left :=
  Iff.rfl

/-- A morphism `Spec(k) ⟶ U/G` of fppf sheaves over `S`. -/
abbrev specToQuotientHom {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) :=
  (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.obj (specOver σ) ⟶
    (ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)

/-- Unfolding of the Hom type of a field-valued point of the fppf quotient sheaf. -/
theorem specToQuotientHom_eq {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) :
    specToQuotientHom ρ σ =
      ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.obj (specOver σ) ⟶
        (ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)) :=
  rfl

/-- `φ : Spec(k') ⟶ U` lifts the field-valued point `f : Spec(k) ⟶ U/G` if the
square with the atlas `U ⟶ U/G` and `Spec(k') ⟶ Spec(k)` commutes. -/
def IsQuotientLift {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) {k : Type u} [Field k]
    {σ : Spec (CommRingCat.of k) ⟶ S} {k' : Type u} [Field k'] [Algebra k k']
    (φ : specExtend σ k' ⟶ U) (f : specToQuotientHom ρ σ) : Prop :=
  (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map φ ≫
      (ofAut ρ).quotientMap (Scheme.fppfTopology.over S) =
    (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map (specExtendToOver σ k') ≫ f

/-- Unfolding of `IsQuotientLift` as commutativity of the atlas square. -/
theorem isQuotientLift_iff {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) {k : Type u} [Field k]
    {σ : Spec (CommRingCat.of k) ⟶ S} {k' : Type u} [Field k'] [Algebra k k']
    (φ : specExtend σ k' ⟶ U) (f : specToQuotientHom ρ σ) :
    IsQuotientLift ρ φ f ↔
      (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map φ ≫
          (ofAut ρ).quotientMap (Scheme.fppfTopology.over S) =
        (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map (specExtendToOver σ k') ≫ f :=
  Iff.rfl


/-- Every field-valued point of a residue-field-free group quotient lifts over a finite
Galois extension, equivariantly for a finite subgroup identified with the Galois group. -/
theorem exists_galoisEquivariantLift {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) [IsResidueFieldFree ρ] {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (f : specToQuotientHom ρ σ) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : IsGalois k k')
      (H : Subgroup G) (_ : Finite H) (e : H ≃* Gal(k'/k))
      (φ : specExtend σ k' ⟶ U),
      IsGalEquivariant ρ e φ ∧ IsQuotientLift ρ φ f := sorry

/-- A finite Galois equivariant point for a finite subgroup of a residue-field-free action
descends to a field-valued quotient point with a commutative lift square. -/
theorem exists_specToQuotient {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) [IsResidueFieldFree ρ] {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) {k' : Type u} [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (H : Subgroup G) [Finite H]
    (e : H ≃* Gal(k'/k)) (φ : specExtend σ k' ⟶ U)
    (hφ : IsGalEquivariant ρ e φ) :
    ∃ f : specToQuotientHom ρ σ, IsQuotientLift ρ φ f := sorry

end AlgebraicGeometry.Scheme.PreRelation
