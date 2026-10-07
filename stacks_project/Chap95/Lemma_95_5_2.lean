module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
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
  (ObjectProperty.EssentiallySmall.exists_set_representatives
    (SheafOfModules.IsFiniteType : ObjectProperty X.Modules) :
    ∃ S : Set X.Modules,
      (∀ M ∈ S, M.IsFiniteType) ∧
      ∀ M : X.Modules, M.IsFiniteType →
        ∃! N : X.Modules, N ∈ S ∧ Nonempty (N ≅ M))

/- The reusable root owner is the essential smallness of the finite-type object property. -/
#synth ObjectProperty.EssentiallySmall
  (SheafOfModules.IsFiniteType : ObjectProperty X.Modules)

#check @SheafOfModules.IsFiniteType.essentiallySmall

/- The representative-set conclusion is available for every essentially small,
isomorphism-closed object property. -/
#check @ObjectProperty.EssentiallySmall.exists_set_representatives

#check @ObjectProperty.EssentiallySmall.of_le

/-- Lemma 95.5.2 (2): the category of finite-type quasi-coherent `𝒪_X`-modules has a set of
isomorphism classes. -/
@[stacks 04U5]
theorem finiteType_quasicoherent_exists_set_representatives :
    ∃ S : Set X.Modules,
      (∀ M ∈ S, M.IsFiniteType ∧ M.IsQuasicoherent) ∧
      ∀ M : X.Modules, M.IsFiniteType → M.IsQuasicoherent →
        ∃! N : X.Modules, N ∈ S ∧ Nonempty (N ≅ M) := sorry

end AlgebraicGeometry.RingedSpace
