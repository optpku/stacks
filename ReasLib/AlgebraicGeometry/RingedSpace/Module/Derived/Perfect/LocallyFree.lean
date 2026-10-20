module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Local
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite locally free models of perfect derived modules

The local-model properties in this file use the canonical derived restriction functor.  They do
not choose a global complex representative of a derived object.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

namespace LocalModel

/-- The generic local-model property specialized to bounded finite locally free complexes. -/
abbrev finiteLocallyFreeOn (K : ModuleDerived X) (U : Opens X.carrier) : Prop :=
  on U
    (fun P : ComplexOn X U ↦
      SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree P) K

/-- The explicit bounded finite locally free representative described by
`finiteLocallyFreeOn K U`. -/
theorem finiteLocallyFreeOn_iff (K : ModuleDerived X) (U : Opens X.carrier) :
    finiteLocallyFreeOn K U ↔
      ∃ P : _root_.CochainComplex (Modules (X.restrict U.isOpenEmbedding)) ℤ,
        ∃ _ : (moduleRestrictionToOpenDerived X U).obj K ≅ DerivedCategory.Q.obj P,
          SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree P := sorry

/-- The object property of admitting bounded finite locally free representatives on an open
cover. -/
@[stacks 0BCJ "(2)"]
abbrev finiteLocallyFree : ObjectProperty (ModuleDerived X) :=
  onCover fun U ↦
    fun P : ComplexOn X U ↦
      SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree P

/-- The open-cover description of `finiteLocallyFree`. -/
theorem mem_finiteLocallyFree_iff (K : ModuleDerived X) :
    finiteLocallyFree K ↔
      ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
        ∀ i : I, finiteLocallyFreeOn K (U i) := sorry

/-- The generic local-model property specialized to bounded finite free complexes. -/
abbrev finiteFreeOn (K : ModuleDerived X) (U : Opens X.carrier) : Prop :=
  on U
    (fun P : ComplexOn X U ↦
      SheafOfModules.CochainComplex.IsBoundedFiniteFree P) K

/-- The explicit bounded finite free representative described by `finiteFreeOn K U`. -/
theorem finiteFreeOn_iff (K : ModuleDerived X) (U : Opens X.carrier) :
    finiteFreeOn K U ↔
      ∃ P : _root_.CochainComplex (Modules (X.restrict U.isOpenEmbedding)) ℤ,
        ∃ _ : (moduleRestrictionToOpenDerived X U).obj K ≅ DerivedCategory.Q.obj P,
          SheafOfModules.CochainComplex.IsBoundedFiniteFree P := sorry

/-- The object property of admitting bounded finite free representatives on an open cover. -/
@[stacks 0BCJ "(3)"]
abbrev finiteFree : ObjectProperty (ModuleDerived X) :=
  onCover fun U ↦
    fun P : ComplexOn X U ↦
      SheafOfModules.CochainComplex.IsBoundedFiniteFree P

/-- The open-cover description of `finiteFree`. -/
theorem mem_finiteFree_iff (K : ModuleDerived X) :
    finiteFree K ↔
      ∃ (I : Type u) (U : I → Opens X.carrier), IsOpenCover U ∧
        ∀ i : I, finiteFreeOn K (U i) := sorry

/-- A bounded finite free local model is a bounded finite locally free local model. -/
theorem finiteLocallyFreeOn_of_finiteFreeOn
    {K : ModuleDerived X} {U : Opens X.carrier} (hK : finiteFreeOn K U) :
    finiteLocallyFreeOn K U := sorry

/-- An open cover by bounded finite free models is an open cover by bounded finite locally free
models. -/
theorem finiteFree_le_finiteLocallyFree :
    finiteFree (X := X) ≤ finiteLocallyFree (X := X) := sorry

/-- Over a ringed space with local stalk rings, perfectness, local bounded finite locally free
models, and local bounded finite free models are equivalent. -/
@[stacks 0BCJ]
theorem perfect_tfae_localModels (K : ModuleDerived X)
    (h_local : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    ([ IsPerfect K, finiteLocallyFree K, finiteFree K ] : List Prop).TFAE := sorry

/-- Over a ringed space with local stalk rings, perfectness is equivalent to admitting bounded
finite locally free models on an open cover. -/
theorem isPerfect_iff_finiteLocallyFree (K : ModuleDerived X)
    (h_local : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    IsPerfect K ↔ finiteLocallyFree K := sorry

/-- Over a ringed space with local stalk rings, perfectness is equivalent to admitting bounded
finite free models on an open cover. -/
theorem isPerfect_iff_finiteFree (K : ModuleDerived X)
    (h_local : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    IsPerfect K ↔ finiteFree K := sorry

/-- Over a ringed space with local stalk rings, bounded finite locally free and bounded finite
free local models give equivalent open-cover conditions. -/
theorem finiteLocallyFree_iff_finiteFree (K : ModuleDerived X)
    (h_local : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    finiteLocallyFree K ↔ finiteFree K := sorry

end LocalModel

end AlgebraicGeometry.RingedSpace.ModuleDerived

namespace SheafOfModules.IsFiniteLocallyFree

variable {X : AlgebraicGeometry.RingedSpace.{u}}

/-- A finite locally free module sheaf, placed in degree zero, is a perfect derived module. -/
@[stacks 01E8 "degree-zero perfectness"]
theorem isPerfect (E : AlgebraicGeometry.RingedSpace.Modules X) [E.IsFiniteLocallyFree] :
    SheafOfModules.IsPerfect E := sorry

end SheafOfModules.IsFiniteLocallyFree
