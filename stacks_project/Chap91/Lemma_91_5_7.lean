module

public import stacks_project.Chap91.Lemma_91_4_4_Obstruction
public import stacks_project.Chap91.Lemma_91_5_7_Comparison
public import stacks_project.Chap91.Lemma_91_5_7_Lift
public import stacks_project.Chap91.Situation_91_6_2_Diagram
import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of a flat lift along a strict morphism of first-order thickenings

For a strict morphism of first-order thickenings and an `𝒪_X`-module flat over `S`, a
flat `𝒪_{X'}`-module lift exists if and only if `f^* 𝒥 ⊗ F ⟶ ℐ ⊗ F` is an isomorphism
and the identity infinitesimal obstruction in `Ext ℱ (ℐ ⊗ F) 2` vanishes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Hom

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable (g : T ⟶ U) (F : T.left.Modules)

/-- Lemma 91.5.7 Let `(f, f')` be a morphism of first-order thickenings as in
Situation 91.3.1. Let `F` be an `𝒪_X`-module. Assume `(f, f')` is a strict morphism of
thickenings and `F` is flat over `S`. There exists an `𝒪_{X'}`-module `F'` flat over `S'`
with `i^* F' ≅ F` if and only if the canonical map `f^* 𝒥 ⊗ F ⟶ ℐ ⊗ F` is an
isomorphism and the class `o(F, ℐ ⊗ F, 1)` in `Ext ℱ (ℐ ⊗ F) 2` of Lemma 91.4.4
vanishes. -/
@[stacks 08LN]
theorem exists_flatLift_iff [SheafOfModules.IsFlatOver F g.left] (hg : IsStrict g)
    [HasExt.{u} T.left.Modules] :
    Nonempty (FlatLift g F) ↔
      IsIso (sourceIdealTensorMap g F) ∧
        existenceObstruction T.hom F (idealModule T.hom ⊗ F)
          (identityInfinitesimalMap T.hom F) = 0 := sorry

end Hom
end AlgebraicGeometry.RingedSpace.Thickening
