module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Locality
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

/- Lemma 29.36.2 (1): affine-open criterion for étaleness. -/
@[stacks 02GJ] #check
  (AlgebraicGeometry.etale_iff :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    Etale f ↔
      ∀ ⦃V : S.Opens⦄, IsAffineOpen V →
        ∀ ⦃U : X.Opens⦄, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
          RingHom.Etale ((f.appLE V U e).hom))

/- Open-cover criterion for étaleness. -/
#check
  (AlgebraicGeometry.Scheme.Hom.etale_iff_exists_openCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    Etale f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, Etale (𝒰.f i ≫ 𝒱.pullbackHom f j))

/- Affine-open-cover criterion for étaleness. -/
#check
  (AlgebraicGeometry.Scheme.Hom.etale_iff_exists_affineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    Etale f ↔
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
          ∀ i : 𝒰.I₀,
            RingHom.Etale (((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom))

/- Restriction to compatible open subschemes preserves étaleness. -/
variable [Etale f]
variable {U : X.Opens} {V : S.Opens} (e : U ≤ f ⁻¹ᵁ V)

#check (inferInstance : Etale (f.resLE V U e))

end

end Scheme.Hom

end AlgebraicGeometry
