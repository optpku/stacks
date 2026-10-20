/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.RingTheory.RingHom.FiniteType.QuasiFinite

/-!
# Local finite-type quasi-finiteness

This file relates local finite type together with finite-fibre local
quasi-finiteness to a local property of ring homomorphisms. It records affine,
open-cover, affine-open-cover, and restriction criteria.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

variable {X S : Scheme.{u}}

/-- A morphism is locally of finite type and locally quasi-finite if and only
if it is locally of finite-type quasi-finite ring homomorphisms. -/
theorem locallyQuasiFinite_iff_locallyOfType
    (f : X ⟶ S) :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
      LocallyOfType RingHom.FiniteType.QuasiFinite f := sorry

/-- Local finite-type quasi-finiteness is detected on every compatible pair
of affine opens by the induced homomorphism on sections. -/
theorem locallyQuasiFinite_iff_forall_affineOpen_appLE
    (f : X ⟶ S) :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
      ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
        ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
          RingHom.FiniteType.QuasiFinite (f.appLE V U e).hom := sorry

/-- Local finite-type quasi-finiteness is equivalent to its validity on open
covers of the target and of each pullback. -/
theorem locallyQuasiFinite_iff_exists_openCover
    (f : X ⟶ S) :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
      ∃ 𝒱 : S.OpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
            ∀ i : 𝒰.I₀,
              LocallyOfFiniteType (𝒰.f i ≫ 𝒱.pullbackHom f j) ∧
                LocallyQuasiFinite (𝒰.f i ≫ 𝒱.pullbackHom f j) := sorry

/-- Local finite-type quasi-finiteness is equivalent to finite-type
quasi-finiteness of the section maps on affine covers of the target and of
each pullback. -/
theorem locallyQuasiFinite_iff_exists_affineOpenCover
    (f : X ⟶ S) :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
      ∃ 𝒱 : S.AffineOpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
            ∀ i : 𝒰.I₀,
              RingHom.FiniteType.QuasiFinite
                (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop.hom := sorry

/-- Restriction to compatible open subschemes preserves local finite-type
quasi-finiteness. -/
theorem locallyQuasiFinite_resLE
    {f : X ⟶ S} (hloc : LocallyOfFiniteType f ∧ LocallyQuasiFinite f)
    {U : X.Opens} {V : S.Opens}
    (e : U ≤ f ⁻¹ᵁ V) :
    LocallyOfFiniteType (f.resLE V U e) ∧
      LocallyQuasiFinite (f.resLE V U e) := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType
