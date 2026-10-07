module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Ring
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

/-!
# Pullback on the Grothendieck ring of vector bundles

This module constructs the contravariant pullback ring homomorphism on the
Grothendieck ring of finite locally free modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.VectorBundleK0

variable {X Y Z : Scheme.{u}}

/-- Pull a finite locally free module back along a morphism of schemes. -/
noncomputable def pullbackObj (f : X ⟶ Y)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules)) :
    ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) :=
  ⟨(Scheme.Modules.pullback f).obj E.obj,
    @Scheme.Modules.pullback_isFiniteLocallyFree X Y f E.obj E.property⟩

/-- The underlying module of `pullbackObj f E` is the ordinary module pullback. -/
theorem pullbackObj_obj (f : X ⟶ Y)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules)) :
    (pullbackObj f E).obj = (Scheme.Modules.pullback f).obj E.obj := sorry

/-- Pullback classes kill the short-exact relations defining vector-bundle `K₀`. -/
theorem relations_le_ker_pullback (f : X ⟶ Y) :
    ObjectProperty.GrothendieckGroup.relations
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules) ≤
      (FreeAbelianGroup.lift fun E : ObjectProperty.FullSubcategory
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules) ↦
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
          (pullbackObj f E)).ker := sorry

/-- The additive pullback on the Grothendieck group of vector bundles. -/
noncomputable def pullbackAdd (f : X ⟶ Y) : VectorBundleK0 Y →+ VectorBundleK0 X :=
  ObjectProperty.GrothendieckGroup.lift
    (fun E ↦ ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) (pullbackObj f E))
    (relations_le_ker_pullback f)

/-- Additive pullback sends a vector-bundle generator to its pulled-back class. -/
theorem pullbackAdd_of (f : X ⟶ Y)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules)) :
    pullbackAdd f (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules) E) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
        (pullbackObj f E) := sorry

/-- Additive pullback preserves the tensor-unit class. -/
theorem pullbackAdd_map_one (f : X ⟶ Y) :
    pullbackAdd f (1 : VectorBundleK0 Y) = 1 := sorry

/-- Additive pullback preserves tensor-induced multiplication. -/
theorem pullbackAdd_map_mul (f : X ⟶ Y) (a b : VectorBundleK0 Y) :
    pullbackAdd f (a * b) = pullbackAdd f a * pullbackAdd f b := sorry

/-- Pullback on the Grothendieck ring of finite locally free modules. -/
noncomputable def pullback (f : X ⟶ Y) : VectorBundleK0 Y →+* VectorBundleK0 X :=
  { pullbackAdd f with
    map_one' := pullbackAdd_map_one f
    map_mul' := pullbackAdd_map_mul f }

/-- The additive part of vector-bundle `K₀` pullback is `pullbackAdd`. -/
theorem pullback_toAddMonoidHom (f : X ⟶ Y) :
    (pullback f).toAddMonoidHom = pullbackAdd f := sorry

/-- Pullback sends a vector-bundle generator to its pulled-back class. -/
theorem pullback_of (f : X ⟶ Y)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules)) :
    pullback f (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules) E) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
        (pullbackObj f E) := sorry

/-- Pullback along the identity is the identity on vector-bundle `K₀`. -/
theorem pullback_id (X : Scheme.{u}) :
    pullback (𝟙 X) = RingHom.id (VectorBundleK0 X) := sorry

/-- Vector-bundle `K₀` pullback is contravariantly functorial under composition. -/
theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) = (pullback f).comp (pullback g) := sorry

end AlgebraicGeometry.Scheme.VectorBundleK0
