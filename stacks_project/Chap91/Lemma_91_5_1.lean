module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Lift
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 91.5.1 Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first-order thickening of ringed
spaces. Let `ℱ'`, `𝒢'` be `𝒪_{X'}`-modules. Set `ℱ = i^* ℱ'` and `𝒢 = i^* 𝒢'`. Let
`φ : ℱ ⟶ 𝒢` be an `𝒪_X`-linear map. The set of lifts of `φ` to an `𝒪_{X'}`-linear map
`φ' : ℱ' ⟶ 𝒢'` is, if nonempty, a principal homogeneous space under
`Hom_{𝒪_X}(ℱ, ℐ𝒢')`. -/
@[stacks 08LH] #check (AlgebraicGeometry.RingedSpace.Hom.ModuleMap.lift_principalHomogeneous :
  ∀ {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]
    {F' G' : X'.Modules} {φ : (i^*).obj F' ⟶ (i^*).obj G'}
    (φ' φ'' : AlgebraicGeometry.RingedSpace.Hom.ModuleMap.Lift F' G' φ),
    ∃! α : (i^*).obj F' ⟶ AlgebraicGeometry.RingedSpace.Hom.idealMulRestrict i G',
      AlgebraicGeometry.RingedSpace.Hom.ModuleMap.Lift.perturb α φ' = φ'')
