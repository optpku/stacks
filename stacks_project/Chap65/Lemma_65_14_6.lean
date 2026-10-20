/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.FieldPoints

/-!
# Field-valued points of the quotient `U/G`
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FieldExtension
open AlgebraicGeometry.Scheme.PreRelation

universe u

/- Lemma 65.14.6 (1): finite Galois equivariant lifts of quotient points. -/
@[stacks 02Z5] #check (AlgebraicGeometry.Scheme.PreRelation.exists_galoisEquivariantLift :
  ∀ {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) [IsResidueFieldFree ρ] {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (f : specToQuotientHom ρ σ),
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : IsGalois k k')
      (H : Subgroup G) (_ : Finite H) (e : H ≃* Gal(k'/k))
      (φ : specExtend σ k' ⟶ U),
      IsGalEquivariant ρ e φ ∧ IsQuotientLift ρ φ f)

/- Lemma 65.14.6 (2): descent of finite Galois equivariant points. -/
@[stacks 02Z5] #check (AlgebraicGeometry.Scheme.PreRelation.exists_specToQuotient :
  ∀ {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) [IsResidueFieldFree ρ] {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) {k' : Type u} [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (H : Subgroup G) [Finite H]
    (e : H ≃* Gal(k'/k)) (φ : specExtend σ k' ⟶ U)
    (_ : IsGalEquivariant ρ e φ),
    ∃ f : specToQuotientHom ρ σ, IsQuotientLift ρ φ f)
