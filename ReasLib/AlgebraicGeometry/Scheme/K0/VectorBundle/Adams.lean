/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.SymmetricPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower.Properties
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Properties

/-!
# The second Adams operation on the Grothendieck ring of vector bundles

The operation is constructed from the generator formula
`[Sym²(E)] - [Λ²(E)]`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.VectorBundleK0

variable {X Y : Scheme.{u}}

/-- The symmetric square of a finite locally free module, as a vector bundle. -/
noncomputable def symmetricSquareObj (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) :=
  ⟨RingedSpace.SymmetricPower.sheaf E.obj 2,
    @SheafOfModules.RingedSite.SymmetricPower.isFiniteLocallyFree
      _ _ _ _ _ _ _ E.obj 2 _ _ E.property⟩

/-- The underlying module of `symmetricSquareObj X E` is `Sym[2] E.obj`. -/
theorem symmetricSquareObj_obj (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    (symmetricSquareObj X E).obj = RingedSpace.SymmetricPower.sheaf E.obj 2 := sorry

/-- The exterior square of a finite locally free module, as a vector bundle. -/
noncomputable def exteriorSquareObj (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) :=
  ⟨RingedSpace.ExteriorPower.sheaf E.obj 2,
    @SheafOfModules.RingedSite.ExteriorPower.isFiniteLocallyFree
      _ _ _ _ _ _ _ E.obj 2 _ _ E.property⟩

/-- The underlying module of `exteriorSquareObj X E` is `Λ[2] E.obj`. -/
theorem exteriorSquareObj_obj (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    (exteriorSquareObj X E).obj = RingedSpace.ExteriorPower.sheaf E.obj 2 := sorry

/-- The second Adams value of a vector bundle is `[Sym²(E)] - [Λ²(E)]`. -/
noncomputable def adamsTwoValue (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    VectorBundleK0 X :=
  ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
      (symmetricSquareObj X E) -
    ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
      (exteriorSquareObj X E)

/-- `adamsTwoValue` is the difference of the symmetric- and exterior-square classes. -/
theorem adamsTwoValue_eq (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    adamsTwoValue X E =
      ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
          (symmetricSquareObj X E) -
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
          (exteriorSquareObj X E) := sorry

/-- Second Adams values kill the short-exact relations defining vector-bundle `K₀`. -/
theorem relations_le_ker_adamsTwo (X : Scheme.{u}) :
    ObjectProperty.GrothendieckGroup.relations
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ≤
      (FreeAbelianGroup.lift (adamsTwoValue X)).ker := sorry

/-- The additive second Adams operation on vector-bundle `K₀`. -/
noncomputable def adamsTwoAdd (X : Scheme.{u}) : VectorBundleK0 X →+ VectorBundleK0 X :=
  ObjectProperty.GrothendieckGroup.lift
    (adamsTwoValue X) (relations_le_ker_adamsTwo X)

/-- The additive second Adams operation evaluates by `[Sym²(E)] - [Λ²(E)]`. -/
theorem adamsTwoAdd_of (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    adamsTwoAdd X (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      adamsTwoValue X E := sorry

/-- The additive second Adams operation preserves the multiplicative unit. -/
theorem adamsTwo_map_one (X : Scheme.{u}) :
    adamsTwoAdd X (1 : VectorBundleK0 X) = 1 := sorry

/-- The additive second Adams operation preserves tensor-induced multiplication. -/
theorem adamsTwo_map_mul (X : Scheme.{u}) (a b : VectorBundleK0 X) :
    adamsTwoAdd X (a * b) = adamsTwoAdd X a * adamsTwoAdd X b := sorry

/-- The second Adams operation on the Grothendieck ring of vector bundles. -/
noncomputable def adamsTwo (X : Scheme.{u}) : VectorBundleK0 X →+* VectorBundleK0 X :=
  { adamsTwoAdd X with
    map_one' := adamsTwo_map_one X
    map_mul' := adamsTwo_map_mul X }

/-- The additive part of `adamsTwo X` is `adamsTwoAdd X`. -/
theorem adamsTwo_toAddMonoidHom (X : Scheme.{u}) :
    (adamsTwo X).toAddMonoidHom = adamsTwoAdd X := sorry

/-- The second Adams operation evaluates by `[Sym²(E)] - [Λ²(E)]` on generators. -/
theorem adamsTwo_of (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    adamsTwo X (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      adamsTwoValue X E := sorry

/-- On an invertible module, the second Adams operation is its tensor-square class. -/
theorem adamsTwo_of_invertible (X : Scheme.{u})
    (L : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules))
    [Scheme.Modules.Invertible L.obj] :
    adamsTwo X (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) L) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
        (tensorObj X L L) := sorry

/-- The second Adams operation commutes with pullback. -/
theorem adamsTwo_pullback (f : X ⟶ Y) :
    (adamsTwo X).comp (pullback f) = (pullback f).comp (adamsTwo Y) := sorry

end AlgebraicGeometry.Scheme.VectorBundleK0
