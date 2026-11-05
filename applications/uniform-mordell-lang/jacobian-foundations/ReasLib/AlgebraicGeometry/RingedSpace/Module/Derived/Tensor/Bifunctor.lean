module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-variable derived tensor on a ringed space

This leaf specializes the generic bifunctorial derived tensor owner to `𝒪_X`-modules.  The
K-flat homotopy-descends condition is the only model assumption needed by the generic source; the
remaining existence statement is kept as the explicit `Has` proof boundary rather than installed
as a global instance.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Tensor

section GlobalSections

variable (X : RingedSpace.{u})

/-- The derived category of modules over the global-sections ring of `X`. -/
@[stacks 0G76 "global-sections derived category"]
abbrev globalSectionsDerived (X : RingedSpace.{u}) :=
  DerivedCategory.{u + 1, u, u + 1}
    (ModuleCat.{u} (AlgebraicGeometry.RingedSpace.globalSectionsRing X))

/-- The canonical two-variable derived tensor over the global-sections ring of `X`. -/
@[stacks 0G76 "global-sections derived tensor bifunctor"]
noncomputable def globalSectionsFunctor :
    globalSectionsDerived X × globalSectionsDerived X ⥤ globalSectionsDerived X :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor
    (C := ModuleCat (AlgebraicGeometry.RingedSpace.globalSectionsRing X))

/-- The curried two-variable derived tensor over the global-sections ring of `X`. -/
@[stacks 0G76 "curried global-sections derived tensor"]
noncomputable abbrev globalSectionsCurried :
    globalSectionsDerived X ⥤ globalSectionsDerived X ⥤ globalSectionsDerived X :=
  Functor.curry.obj (globalSectionsFunctor X)

/-- A fixed factor of the global-sections derived tensor preserves zero morphisms. -/
@[stacks 0G76 "fixed global-sections tensor preserves zero morphisms", instance]
noncomputable instance globalSectionsCurried_obj_preservesZeroMorphisms
    (K : globalSectionsDerived X) :
    ((globalSectionsCurried X).obj K).PreservesZeroMorphisms := sorry

/-- A fixed factor of the global-sections derived tensor preserves binary biproducts. -/
@[stacks 0G76 "global-sections tensor preserves binary biproducts", instance]
noncomputable instance globalSectionsCurried_obj_preservesBinaryBiproduct
    (K A B : globalSectionsDerived X) :
    PreservesBinaryBiproduct A B ((globalSectionsCurried X).obj K) := sorry

/-- The derived tensor of two complexes over the global-sections ring of `X`. -/
@[stacks 0G76 "global-sections derived tensor object"]
noncomputable def globalSectionsObj
    (K L : globalSectionsDerived X) : globalSectionsDerived X :=
  (globalSectionsFunctor X).obj (K, L)

/-- The degree-`n` homology functor on the derived category of global-sections modules. -/
@[stacks 0G77 "global-sections homology functor"]
abbrev globalSectionsHomology (X : RingedSpace.{u}) (n : ℤ) :
    globalSectionsDerived X ⥤ ModuleCat (AlgebraicGeometry.RingedSpace.globalSectionsRing X) :=
  DerivedCategory.homologyFunctor
    (ModuleCat (AlgebraicGeometry.RingedSpace.globalSectionsRing X)) n

/-- The map induced on the two factors of the global-sections derived tensor. -/
@[stacks 0G76 "global-sections derived tensor map"]
noncomputable def globalSectionsMap
    {K K' L L' :
      globalSectionsDerived X}
    (f : K ⟶ K') (g : L ⟶ L') :
    globalSectionsObj X K L ⟶ globalSectionsObj X K' L' :=
  (globalSectionsFunctor X).map (Prod.mkHom f g)

/-- The global-sections derived tensor map sends a pair of identities to an identity. -/
@[simp, stacks 0G76 "global-sections derived tensor identity map"]
theorem globalSectionsMap_id (K L : globalSectionsDerived X) :
    globalSectionsMap X (𝟙 K) (𝟙 L) = 𝟙 (globalSectionsObj X K L) := sorry

/-- The global-sections derived tensor map preserves composition in both variables. -/
@[simp, reassoc, stacks 0G76 "global-sections derived tensor composition"]
theorem globalSectionsMap_comp
    {K K' K'' L L' L'' : globalSectionsDerived X}
    (f : K ⟶ K') (f' : K' ⟶ K'') (g : L ⟶ L') (g' : L' ⟶ L'') :
    globalSectionsMap X (f ≫ f') (g ≫ g') =
      globalSectionsMap X f g ≫ globalSectionsMap X f' g' := sorry

end GlobalSections

section RingedSpace

variable (X : RingedSpace.{u})
variable [AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X]

/-- The existence condition for the two-variable derived tensor of `𝒪_X`-modules. -/
@[stacks 0G76 "ringed-space derived tensor existence"]
abbrev Has : Prop :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.Has (C := Modules X)

/-- The two-variable homotopy tensor source for `𝒪_X`-modules. -/
@[stacks 0G76 "ringed-space homotopy tensor source"]
abbrev sourceFunctor :
    (HomotopyCategory (Modules X) (up ℤ) × HomotopyCategory (Modules X) (up ℤ)) ⥤
      ModuleDerived X :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.sourceFunctor
    (C := Modules X)

/-- Pairs of quasi-isomorphisms used to derive tensor in both variables. -/
@[stacks 0G76 "ringed-space derived tensor denominators"]
abbrev qis : MorphismProperty
    (HomotopyCategory (Modules X) (up ℤ) × HomotopyCategory (Modules X) (up ℤ)) :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.qis (C := Modules X)

/-- The product localization from homotopy modules to derived modules. -/
@[stacks 0G76 "ringed-space derived tensor localization"]
abbrev localization :
    (HomotopyCategory (Modules X) (up ℤ) × HomotopyCategory (Modules X) (up ℤ)) ⥤
      (ModuleDerived X × ModuleDerived X) :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.localization (C := Modules X)

end RingedSpace

section Derived

variable (X : RingedSpace.{u})

/-- The canonical two-variable derived tensor functor on `D(𝒪_X)`. -/
@[stacks 0G76 "ringed-space derived tensor bifunctor"]
noncomputable abbrev functor [Has X] :
    ModuleDerived X × ModuleDerived X ⥤ ModuleDerived X :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.functor (C := Modules X)

/-- The curried canonical two-variable derived tensor on `D(𝒪_X)`. -/
@[stacks 0G76 "curried ringed-space derived tensor"]
noncomputable abbrev curried [Has X] :
    ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X :=
  Functor.curry.obj (functor X)

/-- A fixed factor of the canonical ringed-space derived tensor preserves zero morphisms. -/
@[stacks 0G76 "fixed-factor derived tensor preserves zero morphisms", instance]
noncomputable instance curried_obj_preservesZeroMorphisms [Has X]
    (K : ModuleDerived X) :
    ((curried X).obj K).PreservesZeroMorphisms := sorry

/-- A fixed factor of the canonical ringed-space derived tensor preserves binary biproducts. -/
@[stacks 0G76 "fixed-factor derived tensor preserves binary biproducts", instance]
noncomputable instance curried_obj_preservesBinaryBiproduct
    [Has X] (K A B : ModuleDerived X) :
    PreservesBinaryBiproduct A B ((curried X).obj K) := sorry

/-- The derived tensor of two objects of `D(𝒪_X)`. -/
@[stacks 0G76 "ringed-space derived tensor object"]
noncomputable abbrev obj {X : RingedSpace.{u}} (K L : ModuleDerived X) [Has X] : ModuleDerived X :=
  (functor X).obj (K, L)

/-- The map on the two factors of the derived tensor bifunctor. -/
@[stacks 0G76 "ringed-space derived tensor map"]
noncomputable abbrev map {X : RingedSpace.{u}} {K K' L L' : ModuleDerived X}
    (f : K ⟶ K') (g : L ⟶ L') [Has X] :
    obj K L ⟶ obj K' L' :=
  (functor X).map (Prod.mkHom f g)

/-- The canonical counit from derived tensor to the totalized tensor source. -/
@[stacks 0G76 "ringed-space derived tensor counit"]
noncomputable abbrev counit [Has X] :
    localization X ⋙ functor X ⟶ sourceFunctor X :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.counit (C := Modules X)

/-- Transport the canonical counit to a supplied two-variable derived tensor model. -/
@[stacks 0G76 "ringed-space transported derived tensor counit"]
noncomputable abbrev counitOfIso [Has X]
    (T : ModuleDerived X × ModuleDerived X ⥤ ModuleDerived X)
    (e : functor X ≅ T) : localization X ⋙ T ⟶ sourceFunctor X :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.counitOfIso T e

/-- The canonical isomorphism from the total-left-derived tensor to a supplied model. -/
@[stacks 0G76 "ringed-space derived tensor model isomorphism"]
noncomputable abbrev modelIso [Has X]
    (T : ModuleDerived X × ModuleDerived X ⥤ ModuleDerived X)
    (ε : localization X ⋙ T ⟶ sourceFunctor X)
    [T.IsLeftDerivedFunctor ε (qis X)] : functor X ≅ T :=
  CategoryTheory.DerivedCategory.DerivedTensor.Bifunctor.modelIso T ε

/-- The transported counit agrees with the supplied model counit. -/
@[stacks 0G76 "ringed-space derived tensor model counit"]
theorem counitOfIso_modelIso [Has X]
    (T : ModuleDerived X × ModuleDerived X ⥤ ModuleDerived X)
    (ε : localization X ⋙ T ⟶ sourceFunctor X)
    [T.IsLeftDerivedFunctor ε (qis X)] :
    counitOfIso X T (modelIso X T ε) = ε := sorry

end Derived

/- The `⊗ᴸ` spelling is scoped to this owner; the named `obj` declaration remains the stable API. -/
scoped[RingedSpaceTensor] infixr:70 " ⊗ᴸ " =>
  AlgebraicGeometry.RingedSpace.ModuleDerived.Tensor.obj

end AlgebraicGeometry.RingedSpace.ModuleDerived.Tensor
