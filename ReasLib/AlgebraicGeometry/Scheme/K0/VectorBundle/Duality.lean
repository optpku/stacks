module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Dual

/-!
# Duality on the Grothendieck ring of vector bundles

Dualization of finite locally free modules descends to a ring endomorphism of their
Grothendieck group and commutes with pullback.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.VectorBundleK0

variable {X Y : Scheme.{u}}

/-- Dualize a finite locally free module while retaining its finite locally free property. -/
noncomputable def dualObj (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) :=
  ⟨Scheme.Modules.dual E.obj,
    @Scheme.Modules.IsFiniteLocallyFree.dual X E.obj E.property⟩

/-- The underlying module of `dualObj X E` is the internal-Hom dual of `E.obj`. -/
theorem dualObj_obj (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    (dualObj X E).obj = Scheme.Modules.dual E.obj := sorry

/-- Dual classes kill the short-exact relations defining vector-bundle `K₀`. -/
theorem relations_le_ker_dual (X : Scheme.{u}) :
    ObjectProperty.GrothendieckGroup.relations
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ≤
      (FreeAbelianGroup.lift fun E : ObjectProperty.FullSubcategory
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ↦
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
          (dualObj X E)).ker := sorry

/-- The additive endomorphism of vector-bundle `K₀` induced by dualization. -/
noncomputable def dualAdd (X : Scheme.{u}) : VectorBundleK0 X →+ VectorBundleK0 X :=
  ObjectProperty.GrothendieckGroup.lift
    (fun E ↦ ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) (dualObj X E))
    (relations_le_ker_dual X)

/-- Additive dualization sends a vector-bundle generator to its dual class. -/
theorem dualAdd_of (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    dualAdd X (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
        (dualObj X E) := sorry

/-- Additive dualization preserves the multiplicative unit. -/
theorem dualAdd_map_one (X : Scheme.{u}) :
    dualAdd X (1 : VectorBundleK0 X) = 1 := sorry

/-- Additive dualization preserves tensor-induced multiplication. -/
theorem dualAdd_map_mul (X : Scheme.{u}) (a b : VectorBundleK0 X) :
    dualAdd X (a * b) = dualAdd X a * dualAdd X b := sorry

/-- Dualization on the Grothendieck ring of finite locally free modules. -/
noncomputable def dual (X : Scheme.{u}) : VectorBundleK0 X →+* VectorBundleK0 X :=
  { dualAdd X with
    map_one' := dualAdd_map_one X
    map_mul' := dualAdd_map_mul X }

/-- The additive part of `dual X` is `dualAdd X`. -/
theorem dual_toAddMonoidHom (X : Scheme.{u}) :
    (dual X).toAddMonoidHom = dualAdd X := sorry

/-- Dualization sends a vector-bundle generator to the class of its dual. -/
theorem dual_of (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    dual X (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
        (dualObj X E) := sorry

/-- Dualization on vector-bundle `K₀` commutes with pullback. -/
theorem dual_pullback (f : X ⟶ Y) :
    (dual X).comp (pullback f) = (pullback f).comp (dual Y) := sorry

end AlgebraicGeometry.Scheme.VectorBundleK0
