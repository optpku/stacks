module

public import stacks_project.Chap91.Lemma_91_5_2_Comparison
public import stacks_project.Chap91.Situation_91_6_2_Diagram
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness of modules along a strict morphism of first-order thickenings

For a strict morphism of first-order thickenings, an `𝒪_{X'}`-module whose restriction
to `X` is flat over `S` is flat over `S'` if and only if the canonical map
`f^* 𝒥 ⊗ F ⟶ ℐ F'` is an isomorphism, in which case both factor maps are isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom (actionToIdealMulRestrict)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Hom

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable (g : T ⟶ U) (F' : T.right.Modules)

/-- Lemma 91.5.2 (1) Let `(f, f')` be a morphism of first-order thickenings of ringed spaces
as in Situation 91.3.1. Let `F'` be an `𝒪_{X'}`-module and set `F = i^* F'`. Assume that
`F` is flat over `S` and that `(f, f')` is a strict morphism of thickenings. Then `F'` is
flat over `S'` if and only if the canonical map `f^* 𝒥 ⊗ F ⟶ ℐ F'` is an isomorphism. -/
@[stacks 08LI]
theorem isFlatOver_iff_isIso_sourceIdealMulMap
    [SheafOfModules.IsFlatOver ((T.hom^*).obj F') g.left] (hg : IsStrict g) :
    SheafOfModules.IsFlatOver F' g.right ↔ IsIso (sourceIdealMulMap g F') := sorry

/-- Lemma 91.5.2 (2) Let `(f, f')` be a strict morphism of first-order thickenings of ringed
spaces as in Situation 91.3.1, and let `F'` be an `𝒪_{X'}`-module. If the canonical map
`f^* 𝒥 ⊗ F ⟶ ℐ F'` is an isomorphism, then the first factor
`f^* 𝒥 ⊗ F ⟶ ℐ ⊗ F` is an isomorphism. -/
@[stacks 08LI]
theorem isIso_sourceIdealMap_tensor (hg : IsStrict g)
    [IsIso (sourceIdealMulMap g F')] :
    IsIso (tensorHom (sourceIdealMap g) (𝟙 ((T.hom^*).obj F'))) := sorry

/-- Lemma 91.5.2 (3) Let `(f, f')` be a strict morphism of first-order thickenings of ringed
spaces as in Situation 91.3.1, and let `F'` be an `𝒪_{X'}`-module. If the canonical map
`f^* 𝒥 ⊗ F ⟶ ℐ F'` is an isomorphism, then the second factor
`ℐ ⊗ F ⟶ ℐ F'` is an isomorphism. -/
@[stacks 08LI]
theorem isIso_actionToIdealMulRestrict (hg : IsStrict g)
    [IsIso (sourceIdealMulMap g F')] :
    IsIso (actionToIdealMulRestrict T.hom F') := sorry

end Hom
end AlgebraicGeometry.RingedSpace.Thickening
