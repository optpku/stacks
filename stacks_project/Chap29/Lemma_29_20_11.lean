/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Local
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.20.11: local finite-type quasi-finiteness is equivalent to
finite-type quasi-finiteness on every compatible pair of affine opens; it also
has open-cover and affine-open-cover criteria and is preserved by restriction. -/
@[stacks 01TK] #check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.locallyQuasiFinite_iff_forall_affineOpen_appLE :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
        ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
          ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
            RingHom.FiniteType.QuasiFinite (f.appLE V U e).hom)

/- Open-cover criterion for local finite-type quasi-finiteness. -/
#check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.locallyQuasiFinite_iff_exists_openCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
        ∃ 𝒱 : S.OpenCover,
          ∀ j : 𝒱.I₀,
            ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
              ∀ i : 𝒰.I₀,
                LocallyOfFiniteType (𝒰.f i ≫ 𝒱.pullbackHom f j) ∧
                  LocallyQuasiFinite (𝒰.f i ≫ 𝒱.pullbackHom f j))

/- Affine-open-cover criterion for local finite-type quasi-finiteness. -/
#check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.locallyQuasiFinite_iff_exists_affineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
        ∃ 𝒱 : S.AffineOpenCover,
          ∀ j : 𝒱.I₀,
            ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
              ∀ i : 𝒰.I₀,
                RingHom.FiniteType.QuasiFinite
                  (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop.hom)

/- Restriction stability for local finite-type quasi-finiteness. -/
#check
  (AlgebraicGeometry.Scheme.Hom.FiniteType.locallyQuasiFinite_resLE :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S},
      LocallyOfFiniteType f ∧ LocallyQuasiFinite f →
        ∀ {U : X.Opens} {V : S.Opens} (e : U ≤ f ⁻¹ᵁ V),
          LocallyOfFiniteType (f.resLE V U e) ∧
            LocallyQuasiFinite (f.resLE V U e))
