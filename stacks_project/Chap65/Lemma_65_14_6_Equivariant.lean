/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Notation
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import stacks_project.Chap65.Lemma_65_14_3_Relation

/-!
# Galois-equivariant lifts of field-valued points of `U/G`

This module records `Spec(k)` and `Spec(k')` as schemes over `S`, the action of
`Gal(k'/k)` on `Spec(k')`, and the sheaf-morphism type of a field-valued point of
the fppf quotient sheaf of `ofAut ρ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- `Spec(k)` as a scheme over `S` via a structure morphism `σ`. -/
abbrev specOver {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) : Over S :=
  Over.mk σ

/-- The object `specOver σ` is `Over.mk σ`. -/
theorem specOver_eq {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) :
    specOver σ = Over.mk σ := sorry

/-- `Spec(k')` as a scheme over `S`, via `Spec(k') ⟶ Spec(k) ⟶ S`. -/
def specExtend {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (k' : Type u) [Field k'] [Algebra k k'] :
    Over S :=
  Over.mk (FieldExtension.specMap k k' ≫ σ)

/-- The structure morphism of `specExtend σ k'` is the composite
`FieldExtension.specMap k k' ≫ σ`. -/
theorem specExtend_hom {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (k' : Type u) [Field k'] [Algebra k k'] :
    (specExtend σ k').hom = FieldExtension.specMap k k' ≫ σ := sorry

/-- The morphism `Spec(k') ⟶ Spec(k)` of schemes over `S`. -/
def specExtendToOver {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (k' : Type u) [Field k'] [Algebra k k'] :
    specExtend σ k' ⟶ specOver σ :=
  Over.homMk (FieldExtension.specMap k k')

/-- The underlying scheme morphism of `specExtendToOver σ k'` is
`FieldExtension.specMap k k'`. -/
theorem specExtendToOver_left {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (k' : Type u) [Field k'] [Algebra k k'] :
    (specExtendToOver σ k').left = FieldExtension.specMap k k' := sorry

/-- The scheme morphism `Spec(k') ⟶ Spec(k')` induced by a Galois automorphism. -/
def galSpecMap {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (g : Gal(k'/k)) :
    Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k') :=
  Spec.map (CommRingCat.ofHom g.toRingHom)

/-- `galSpecMap` is `Spec.map` of the underlying ring homomorphism. -/
theorem galSpecMap_eq {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (g : Gal(k'/k)) :
    galSpecMap g = Spec.map (CommRingCat.ofHom g.toRingHom) := sorry

/-- A Galois automorphism of `k'/k` acts on `Spec(k')` over `Spec(k)`. -/
theorem galSpecMap_comp_specMap {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (g : Gal(k'/k)) :
    galSpecMap g ≫ FieldExtension.specMap k k' = FieldExtension.specMap k k' :=
  sorry

/-- The left action of `Gal(k'/k)` on `Spec(k')`, sending `g` to `galSpecMap (g⁻¹)`.
`g ↦ galSpecMap g` is only an anti-homomorphism because `Spec.map` is contravariant. -/
def galSpecAut {k k' : Type u} [Field k] [Field k'] [Algebra k k'] :
    Gal(k'/k) →* Aut (Spec (CommRingCat.of k')) where
  toFun g :=
    { hom := galSpecMap (g⁻¹)
      inv := galSpecMap g
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- The underlying scheme morphism of `galSpecAut g` is `galSpecMap (g⁻¹)`. -/
theorem galSpecAut_hom {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (g : Gal(k'/k)) :
    (galSpecAut g).hom = galSpecMap (g⁻¹) := sorry

/-- Equivariance of `φ : Spec(k') ⟶ U` for a subgroup `H ≤ G` identified with
`Gal(k'/k)`: the left action of `e h` on `Spec(k')` is `galSpecMap ((e h)⁻¹)`,
since `g ↦ galSpecMap g` is contravariant, and this intertwines with `ρ h`. -/
def IsGalEquivariant {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {H : Subgroup G} (e : H ≃* Gal(k'/k))
    {σ : Spec (CommRingCat.of k) ⟶ S} (φ : specExtend σ k' ⟶ U) : Prop :=
  ∀ h : H, galSpecMap ((e h)⁻¹) ≫ φ.left = φ.left ≫ (ρ (h : G)).hom.left

/-- Unfolding of `IsGalEquivariant` as the scheme-level intertwining identity. -/
theorem isGalEquivariant_iff {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {H : Subgroup G} (e : H ≃* Gal(k'/k))
    {σ : Spec (CommRingCat.of k) ⟶ S} (φ : specExtend σ k' ⟶ U) :
    IsGalEquivariant ρ e φ ↔
      ∀ h : H, galSpecMap ((e h)⁻¹) ≫ φ.left = φ.left ≫ (ρ (h : G)).hom.left :=
  sorry

/-- A morphism `Spec(k) ⟶ U/G` of fppf sheaves over `S`. -/
abbrev specToQuotientHom {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) [IsResidueFieldFree ρ] {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) :=
  (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.obj (specOver σ) ⟶
    (ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)

/-- Unfolding of the Hom type of a field-valued point of the fppf quotient sheaf. -/
theorem specToQuotientHom_eq {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) [IsResidueFieldFree ρ] {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) :
    specToQuotientHom ρ σ =
      ((Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.obj (specOver σ) ⟶
        (ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)) :=
  sorry

/-- `φ : Spec(k') ⟶ U` lifts the field-valued point `f : Spec(k) ⟶ U/G` if the
square with the atlas `U ⟶ U/G` and `Spec(k') ⟶ Spec(k)` commutes. -/
def IsQuotientLift {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) [IsResidueFieldFree ρ] {k : Type u} [Field k]
    {σ : Spec (CommRingCat.of k) ⟶ S} {k' : Type u} [Field k'] [Algebra k k']
    (φ : specExtend σ k' ⟶ U) (f : specToQuotientHom ρ σ) : Prop :=
  (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map φ ≫
      (ofAut ρ).quotientMap (Scheme.fppfTopology.over S) =
    (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map (specExtendToOver σ k') ≫ f

/-- Unfolding of `IsQuotientLift` as commutativity of the atlas square. -/
theorem isQuotientLift_iff {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) [IsResidueFieldFree ρ] {k : Type u} [Field k]
    {σ : Spec (CommRingCat.of k) ⟶ S} {k' : Type u} [Field k'] [Algebra k k']
    (φ : specExtend σ k' ⟶ U) (f : specToQuotientHom ρ σ) :
    IsQuotientLift ρ φ f ↔
      (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map φ ≫
          (ofAut ρ).quotientMap (Scheme.fppfTopology.over S) =
        (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.map (specExtendToOver σ k') ≫ f :=
  sorry

end AlgebraicGeometry.Scheme.PreRelation
