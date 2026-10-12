/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_14_6_Equivariant

/-!
# Field-valued points of the quotient `U/G`
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PreRelation

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- Lemma 65.14.6 (1): notation and assumptions as in Lemma 65.14.3. If
`Spec(k) ⟶ U/G` is a morphism of fppf sheaves over `S`, then there exist a finite
Galois extension `k'/k`, a finite subgroup `H ≤ G`, an isomorphism
`H ≃* Gal(k'/k)`, and an `H`-equivariant morphism `Spec(k') ⟶ U` lifting that
field-valued point along `U ⟶ U/G`. -/
@[stacks 02Z5]
theorem exists_galoisEquivariantLift {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) [IsResidueFieldFree ρ] {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (f : specToQuotientHom ρ σ) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : IsGalois k k')
      (H : Subgroup G) (_ : Finite H) (e : H ≃* Gal(k'/k))
      (φ : specExtend σ k' ⟶ U),
      IsGalEquivariant ρ e φ ∧ IsQuotientLift ρ φ f := sorry

/-- Lemma 65.14.6 (2): conversely, a finite Galois extension `k'/k`, a finite
subgroup `H ≤ G`, an isomorphism `H ≃* Gal(k'/k)`, and an `H`-equivariant
morphism `Spec(k') ⟶ U` determine a morphism `Spec(k) ⟶ U/G` which that
morphism lifts. -/
@[stacks 02Z5]
theorem exists_specToQuotient {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) [IsResidueFieldFree ρ] {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) {k' : Type u} [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (H : Subgroup G) [Finite H]
    (e : H ≃* Gal(k'/k)) (φ : specExtend σ k' ⟶ U)
    (hφ : IsGalEquivariant ρ e φ) :
    ∃ f : specToQuotientHom ρ σ, IsQuotientLift ρ φ f := sorry

end AlgebraicGeometry.Scheme.PreRelation
