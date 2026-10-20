/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Over
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation

/-!
# Coproduct relations from abstract group automorphisms

This module records the pre-relation `R = ∐_G U` associated to a homomorphism
`G →* Aut U` of an abstract group into automorphisms of a scheme `U` over `S`,
together with the residue-field freeness hypothesis used to obtain an étale
equivalence relation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The coproduct `R = ∐_{g : G} U` of copies of `U` indexed by `G`, taken in `Over S`. -/
def relationOver {S : Scheme.{u}} (U : Over S) (G : Type u) : Over S :=
  ∐ fun _ : G ↦ U

/-- The relation object is the coproduct of copies of `U` indexed by `G`. -/
theorem relationOver_eq {S : Scheme.{u}} (U : Over S) (G : Type u) :
    relationOver U G = ∐ fun _ : G ↦ U := sorry

/-- The morphism `j : R ⟶ U ⨯ U` sending the `g`-summand by `(g(x), x)`, i.e. the
product lift of `(ρ g).hom` and `𝟙 U`. -/
def relationHom {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) : relationOver U G ⟶ U ⨯ U :=
  Sigma.desc fun g ↦ prod.lift (ρ g).hom (𝟙 U)

/-- The defining map of the relation is the coproduct fold of the graphs
`(ρ g).hom, 𝟙 U`. -/
theorem relationHom_eq {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) :
    relationHom ρ = Sigma.desc fun g ↦ prod.lift (ρ g).hom (𝟙 U) := sorry

/-- On the `g`-summand, `j` is the pair `((ρ g).hom, 𝟙 U)`. -/
theorem relationHom_ι {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) (g : G) :
    Sigma.ι (fun _ : G ↦ U) g ≫ relationHom ρ = prod.lift (ρ g).hom (𝟙 U) := sorry

/-- The pre-relation on `U` over `S` with source `R = ∐_G U` and defining map
`j : R ⟶ U ⨯ U`, `(g, x) ↦ (g(x), x)`. -/
def ofAut {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) : PreRelation U :=
  ofHom (relationHom ρ)

/-- The defining arrow of `ofAut ρ` is `relationHom ρ`. -/
theorem ofAut_hom {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) : (ofAut ρ).hom = relationHom ρ := sorry

/-- The first projection of `ofAut ρ`, restricted to the `g`-summand, is the
automorphism `(ρ g).hom`. -/
theorem ofAut_t_ι {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) (g : G) :
    Sigma.ι (fun _ : G ↦ U) g ≫ (ofAut ρ).t = (ρ g).hom := sorry

/-- The second projection of `ofAut ρ`, restricted to the `g`-summand, is the
identity on `U`. -/
theorem ofAut_s_ι {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) (g : G) :
    Sigma.ι (fun _ : G ↦ U) g ≫ (ofAut ρ).s = 𝟙 U := sorry

/-- The endomorphism of `κ(u)` induced by an automorphism that fixes the point `u`. -/
def residueFieldAut {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) (g : G) {u : U.left} (hu : (ρ g).hom.left u = u) :
    U.left.residueField u ⟶ U.left.residueField u :=
  (U.left.residueFieldCongr hu.symm).hom ≫ (ρ g).hom.left.residueFieldMap u

/-- The induced residue-field map is the composite of `residueFieldCongr` along the
fixed-point identification with `residueFieldMap`. -/
theorem residueFieldAut_eq {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) (g : G) {u : U.left} (hu : (ρ g).hom.left u = u) :
    residueFieldAut ρ g hu =
      (U.left.residueFieldCongr hu.symm).hom ≫
        (ρ g).hom.left.residueFieldMap u := sorry

/-- The identity element of `G` acts by the identity automorphism of `U` over `S`. -/
theorem ofAut_one_hom {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) : (ρ 1).hom = 𝟙 U := sorry

/-- The identity automorphism of `U` over `S` fixes every point of `U`. -/
theorem ofAut_one_left_apply {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) (u : U.left) : (ρ 1).hom.left u = u := sorry

/-- The identity element induces the identity on every residue field. -/
theorem residueFieldAut_one {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) (u : U.left) :
    residueFieldAut ρ 1 (ofAut_one_left_apply ρ u) = 𝟙 (U.left.residueField u) := sorry

/-- An action is residue-field free if every non-identity element fixing a point of `U`
induces a nontrivial automorphism of its residue field. -/
@[mk_iff]
class IsResidueFieldFree {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) : Prop where
  /-- A non-identity group element fixing `u` acts nontrivially on `κ(u)`. -/
  residueFieldAut_ne_id :
    ∀ (u : U.left) (g : G), g ≠ 1 → ∀ (hu : (ρ g).hom.left u = u),
      residueFieldAut ρ g hu ≠ 𝟙 (U.left.residueField u)

/-- A homomorphism from a subsingleton group is residue-field free, since no
non-identity element exists. -/
instance instIsResidueFieldFree_subsingleton {S : Scheme.{u}} {U : Over S}
    {G : Type u} [Group G] [Subsingleton G] (ρ : G →* Aut U) :
    IsResidueFieldFree ρ := sorry

/-- The first projection of `ofAut ρ` is étale, as a coproduct of isomorphisms. -/
instance instEtale_t_ofAut {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) : Etale (ofAut ρ).t.left := sorry

/-- The second projection of `ofAut ρ` is étale, as a coproduct of identities. -/
instance instEtale_s_ofAut {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) : Etale (ofAut ρ).s.left := sorry

/-- A residue-field free action defines an étale equivalence
relation on `U` over `S`. -/
instance instIsEtaleEquivalenceRelation_ofAut {S : Scheme.{u}} {U : Over S}
    {G : Type u} [Group G] (ρ : G →* Aut U) [IsResidueFieldFree ρ] :
    (ofAut ρ).IsEtaleEquivalenceRelation := sorry

end AlgebraicGeometry.Scheme.PreRelation
