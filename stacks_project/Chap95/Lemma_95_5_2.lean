module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteType.Small
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})

/- Lemma 95.5.2 (1): the category of finite-type `𝒪_X`-modules has a set of isomorphism
classes. -/
@[stacks 04U5]
#check
  (CategoryTheory.ObjectProperty.EssentiallySmall.exists_set_representatives
    (SheafOfModules.IsFiniteType (R := X.ringCatSheaf) : ObjectProperty X.Modules) :
    ∃ S : Set X.Modules,
      (∀ M ∈ S, M.IsFiniteType) ∧
      ∀ M : X.Modules, M.IsFiniteType →
        ∃! N : X.Modules, N ∈ S ∧ Nonempty (N ≅ M))

/- Lemma 95.5.2 (2): the category of finite-type quasi-coherent `𝒪_X`-modules has a set of
isomorphism classes. -/
@[stacks 04U5]
#check
  (CategoryTheory.ObjectProperty.EssentiallySmall.exists_set_representatives
    ((SheafOfModules.IsFiniteType (R := X.ringCatSheaf) : ObjectProperty X.Modules) ⊓
      X.quasiCoherentModuleProperty) :
    ∃ S : Set X.Modules,
      (∀ M ∈ S, M.IsFiniteType ∧ M.IsQuasicoherent) ∧
      ∀ M : X.Modules, M.IsFiniteType ∧ M.IsQuasicoherent →
        ∃! N : X.Modules, N ∈ S ∧ Nonempty (N ≅ M))

end AlgebraicGeometry.RingedSpace
