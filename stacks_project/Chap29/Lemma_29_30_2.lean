/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Locality
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/- Lemma 29.30.2 (1) -/
@[stacks 01UD]
#check (AlgebraicGeometry.Scheme.Hom.syntomic_iff_affineOpen_appLE_syntomic f :
  Syntomic f ↔
    ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
      ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
        RingHom.Syntomic ((f.appLE V U e).hom))

/- Lemma 29.30.2 (2) -/
@[stacks 01UD]
#check (AlgebraicGeometry.Scheme.Hom.syntomic_iff_exists_openCover_preimageOpenCover f :
  Syntomic f ↔
    ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
      ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
        ∀ i : 𝒰.I₀, Syntomic ((𝒰.f i) ≫ (𝒱.pullbackHom f j)))

/- Lemma 29.30.2 (3) -/
@[stacks 01UD]
#check (AlgebraicGeometry.Scheme.Hom.syntomic_iff_exists_affineOpenCover_preimageAffineOpenCover f :
  Syntomic f ↔
    ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
      ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
        ∀ i : 𝒰.I₀,
          RingHom.Syntomic ((((𝒰.f i) ≫ (𝒱.openCover.pullbackHom f j)).appTop).hom))

/- Lemma 29.30.2 (4) -/
@[stacks 01UD]
#check (AlgebraicGeometry.Scheme.Hom.syntomic_resLE_of_syntomic f :
  Syntomic f → ∀ {U : X.Opens} {V : S.Opens}
    (e : U ≤ f ⁻¹ᵁ V), Syntomic (f.resLE V U e))

end AlgebraicGeometry.Scheme.Hom
