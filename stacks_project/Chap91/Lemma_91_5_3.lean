module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Lift.Relative
import StacksCheckRecall

/-!
# Lifts of maps of modules along a strict morphism of first-order thickenings

In Situation 91.3.1, if `𝒢'` is flat over `S'` and `(f, f')` is strict, the type of
`𝒪_{X'}`-linear lifts of an `𝒪_X`-linear map `φ : i^* ℱ' ⟶ i^* 𝒢'` is, if nonempty, a
principal homogeneous space under `Hom_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Hom.ModuleMap
open AlgebraicGeometry.RingedSpace.Thickening.Hom
open AlgebraicGeometry.RingedSpace.Thickening.Hom.ModuleMap
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 91.5.3 Let `(f, f')` be a morphism of first-order thickenings as in
Situation 91.3.1. Let `ℱ'`, `𝒢'` be `𝒪_{X'}`-modules and set `ℱ = i^* ℱ'` and
`𝒢 = i^* 𝒢'`. Let `φ : ℱ ⟶ 𝒢` be an `𝒪_X`-linear map. Assume that `𝒢'` is flat
over `S'` and that `(f, f')` is a strict morphism of thickenings. The set of
lifts of `φ` to an `𝒪_{X'}`-linear map `φ' : ℱ' ⟶ 𝒢'` is, if nonempty, a
principal homogeneous space under `Hom_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)`. -/
@[stacks 08LJ] #check
  (AlgebraicGeometry.RingedSpace.Thickening.Hom.ModuleMap.lift_principalHomogeneous :
    ∀ {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
      (g : T ⟶ U) {F' G' : T.right.Modules}
      {φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G'}
      [SheafOfModules.IsFlatOver G' g.right],
      IsStrict g → ∀ (φ' φ'' : Lift F' G' φ),
      ∃! α : (T.hom^*).obj F' ⟶
        (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom),
        relativePerturb g α φ' = φ'')
