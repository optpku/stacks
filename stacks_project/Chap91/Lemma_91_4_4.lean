module

public import stacks_project.Chap91.Lemma_91_4_4_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence obstruction for mixed-scalar module extensions

Along a first-order thickening of ringed spaces, a prescribed infinitesimal comparison
`c : ℐ ⊗ ℱ ⟶ 𝒦` of `𝒪_X`-modules admits an 08L4 sequence if and only if the canonical
class `existenceObstruction i F K c` in `Ext ℱ 𝒦 2` vanishes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules
namespace InfinitesimalExtension

variable {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]
variable (F K : X.Modules)
variable (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
variable [HasExt.{u} X.Modules]

/-- Lemma 91.4.4: Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first-order thickening of
ringed spaces. Given `𝒪_X`-modules `ℱ`, `𝒦` and an `𝒪_X`-linear map
`c : ℐ ⊗ ℱ ⟶ 𝒦` (recovered from the pushforward comparison by
`infinitesimalMap_restrict`), there is a canonical class
`existenceObstruction i F K c` in `Ext ℱ 𝒦 2` whose vanishing is necessary and
sufficient for the existence of an 08L4 sequence with infinitesimal map `c`. -/
@[stacks 08L8]
theorem existenceObstruction_eq_zero_iff :
    existenceObstruction i F K c = 0 ↔
      Nonempty (InfinitesimalExtension i F K c) := sorry

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
