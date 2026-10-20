/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Data.Finite.Defs

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}}
variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [HasCoproducts.{u} (Sheaf X.smallEtaleTopology (Type (u + 1)))]

/-- A sheaf of sets on the small étale site is a finite coproduct of sheafified representables
associated to quasi-compact and quasi-separated étale objects. -/
def IsFiniteCoproductOfQcQsSheafifiedRepresentable
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) : Prop :=
  ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Etale),
    (∀ i, (CompactSpace (U i).left ∧ QuasiSeparatedSpace (U i).left)) ∧
      Nonempty (F ≅ ∐ fun i ↦ X.smallEtaleTopology.sheafifiedRepresentable (U i))

/-- A finite coproduct of sheafified representables is characterized by its finite index type,
quasi-compact and quasi-separated étale objects, and an isomorphism to the coproduct. -/
theorem isFiniteCoproductOfQcQsSheafifiedRepresentable_iff
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    IsFiniteCoproductOfQcQsSheafifiedRepresentable F ↔
      ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Etale),
        (∀ i, (CompactSpace (U i).left ∧ QuasiSeparatedSpace (U i).left)) ∧
          Nonempty (F ≅ ∐ fun i ↦ X.smallEtaleTopology.sheafifiedRepresentable (U i)) := sorry

/-- A sheaf of sets on the small étale site has a finite coequalizer presentation by sheafified
representables associated to quasi-compact and quasi-separated étale objects. -/
def IsCoequalizerOfQcQsSheafifiedRepresentable
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) : Prop :=
  ∃ (F0 F1 : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (f g : F1 ⟶ F0) (_ : HasCoequalizer f g),
    IsFiniteCoproductOfQcQsSheafifiedRepresentable F0 ∧
      IsFiniteCoproductOfQcQsSheafifiedRepresentable F1 ∧
        Nonempty (F ≅ coequalizer f g)

/-- A finite coequalizer presentation is characterized by a parallel pair with coequalizer whose
two objects are finite coproducts of quasi-compact and quasi-separated sheafified representables. -/
theorem isCoequalizerOfQcQsSheafifiedRepresentable_iff
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    IsCoequalizerOfQcQsSheafifiedRepresentable F ↔
      ∃ (F0 F1 : Sheaf X.smallEtaleTopology (Type (u + 1)))
        (f g : F1 ⟶ F0) (_ : HasCoequalizer f g),
        IsFiniteCoproductOfQcQsSheafifiedRepresentable F0 ∧
          IsFiniteCoproductOfQcQsSheafifiedRepresentable F1 ∧
            Nonempty (F ≅ coequalizer f g) := sorry

/-- For a quasi-compact and quasi-separated scheme, constructible set-valued étale sheaves are
exactly those admitting finite coequalizer presentations by quasi-compact and quasi-separated
sheafified representables. -/
theorem isConstructibleEtaleSet_iff_coequalizerPresentation
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    IsConstructibleEtaleSet
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstant G) F ↔
      IsCoequalizerOfQcQsSheafifiedRepresentable F := sorry

/-- For a quasi-compact and quasi-separated scheme, the constructible and finite coequalizer
object predicates on set-valued étale sheaves are equal. -/
theorem constructibleEtaleSet_eq_isCoequalizerOfQcQsSheafifiedRepresentable
    [CompactSpace X] [QuasiSeparatedSpace X] :
    (fun F ↦ IsConstructibleEtaleSet
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstant G) F) =
      IsCoequalizerOfQcQsSheafifiedRepresentable := sorry

end CategoryTheory.Sheaf
