module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Ring
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Properties

/-!
# The ring structure on the Grothendieck group of vector bundles

Tensor product gives the Grothendieck group of finite locally free modules on a scheme its
canonical commutative-ring structure, and the comparison with perfect-complex `K₀` is a ring
homomorphism.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.VectorBundleK0

/-- The tensor product of two finite locally free modules. -/
noncomputable def tensorObj (X : Scheme.{u})
    (E F : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) :=
  ⟨CategoryTheory.MonoidalCategory.tensorObj E.obj F.obj,
    @SheafOfModules.IsFiniteLocallyFree.tensor _ _ _ _ _ _ _ _ _
      E.obj F.obj E.property F.property⟩

/-- The underlying module of `VectorBundleK0.tensorObj` is the ordinary tensor product. -/
theorem tensorObj_obj (X : Scheme.{u})
    (E F : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    (tensorObj X E F).obj =
      CategoryTheory.MonoidalCategory.tensorObj E.obj F.obj := sorry

/-- The finite locally free structure module. -/
noncomputable def unitObject (X : Scheme.{u}) :
    ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) :=
  ⟨(SheafOfModules.unit X.toRingedSpace.ringCatSheaf : X.Modules),
    inferInstance⟩

/-- The underlying module of `VectorBundleK0.unitObject` is the structure module. -/
theorem unitObject_obj (X : Scheme.{u}) :
    (unitObject X).obj =
      (SheafOfModules.unit X.toRingedSpace.ringCatSheaf : X.Modules) := sorry

/-- Tensoring with a fixed vector bundle kills the exact-sequence relations in the other
variable. -/
theorem relations_le_ker_mulOf (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    ObjectProperty.GrothendieckGroup.relations
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ≤
      (FreeAbelianGroup.lift fun F : ObjectProperty.FullSubcategory
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ↦
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
          (tensorObj X E F)).ker := sorry

/-- Multiplication by the class of a fixed finite locally free module. -/
noncomputable def mulOf (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    VectorBundleK0 X →+ VectorBundleK0 X :=
  ObjectProperty.GrothendieckGroup.lift
    (fun F ↦ ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) (tensorObj X E F))
    (relations_le_ker_mulOf X E)

/-- `VectorBundleK0.mulOf` sends a generator to its tensor-product class. -/
theorem mulOf_of (X : Scheme.{u})
    (E F : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    mulOf X E (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) F) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
        (tensorObj X E F) := sorry

/-- Vector-bundle classes defining `VectorBundleK0.mulOf` kill the exact-sequence relations. -/
theorem relations_le_ker_mul (X : Scheme.{u}) :
    ObjectProperty.GrothendieckGroup.relations
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ≤
      (FreeAbelianGroup.lift fun E : ObjectProperty.FullSubcategory
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) ↦ mulOf X E).ker := sorry

/-- The biadditive multiplication on vector-bundle `K₀`, induced by tensor product. -/
noncomputable def mul (X : Scheme.{u}) :
    VectorBundleK0 X →+ VectorBundleK0 X →+ VectorBundleK0 X :=
  ObjectProperty.GrothendieckGroup.lift (mulOf X) (relations_le_ker_mul X)

/-- Multiplication of vector-bundle generators is represented by tensor product. -/
theorem mul_of (X : Scheme.{u})
    (E F : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    mul X
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E)
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) F) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
        (tensorObj X E F) := sorry

/-- Multiplication on `VectorBundleK0 X` is induced by tensor product. -/
noncomputable instance instMul (X : Scheme.{u}) : Mul (VectorBundleK0 X) :=
  ⟨fun x y ↦ mul X x y⟩

/-- The unit on `VectorBundleK0 X` is the class of the structure module. -/
noncomputable instance instOne (X : Scheme.{u}) : One (VectorBundleK0 X) :=
  ⟨ObjectProperty.GrothendieckGroup.of
    (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) (unitObject X)⟩

/-- Tensor multiplication on `VectorBundleK0 X` is associative. -/
theorem mul_assoc_axiom (X : Scheme.{u}) (a b c : VectorBundleK0 X) :
    a * b * c = a * (b * c) := sorry

/-- Tensor multiplication on `VectorBundleK0 X` is commutative. -/
theorem mul_comm_axiom (X : Scheme.{u}) (a b : VectorBundleK0 X) : a * b = b * a := sorry

/-- The structure-module class is a left unit for vector-bundle multiplication. -/
theorem one_mul_axiom (X : Scheme.{u}) (a : VectorBundleK0 X) : 1 * a = a := sorry

/-- Tensor multiplication on `VectorBundleK0 X` distributes over addition. -/
theorem mul_add_axiom (X : Scheme.{u}) (a b c : VectorBundleK0 X) :
    a * (b + c) = a * b + a * c := sorry

/-- The canonical commutative-ring structure on vector-bundle `K₀`. -/
noncomputable instance instCommRing (X : Scheme.{u}) : CommRing (VectorBundleK0 X) :=
  CommRing.ofMinimalAxioms add_assoc zero_add neg_add_cancel
    (mul_assoc_axiom X) (mul_comm_axiom X) (one_mul_axiom X) (mul_add_axiom X)

/-- The multiplicative unit in `VectorBundleK0 X` is the structure-module class. -/
theorem one_eq (X : Scheme.{u}) :
    (1 : VectorBundleK0 X) = ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) (unitObject X) := sorry

/-- The additive comparison preserves the multiplicative unit. -/
theorem toK0_map_one (X : Scheme.{u}) : toK0 X 1 = 1 := sorry

/-- The additive comparison preserves tensor-induced multiplication. -/
theorem toK0_map_mul (X : Scheme.{u}) (a b : VectorBundleK0 X) :
    toK0 X (a * b) = toK0 X a * toK0 X b := sorry

/-- The comparison from vector-bundle `K₀` to perfect-complex `K₀` as a ring homomorphism. -/
noncomputable def toK0RingHom (X : Scheme.{u}) : VectorBundleK0 X →+* K0 X where
  toFun := toK0 X
  map_one' := toK0_map_one X
  map_mul' := toK0_map_mul X
  map_zero' := (toK0 X).map_zero
  map_add' := (toK0 X).map_add

/-- The additive part of `toK0RingHom` is the canonical comparison map. -/
theorem toK0RingHom_toAddMonoidHom (X : Scheme.{u}) :
    (toK0RingHom X).toAddMonoidHom = toK0 X := sorry

/-- The ring comparison preserves vector-bundle generators. -/
theorem toK0RingHom_of (X : Scheme.{u})
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)) :
    toK0RingHom X (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      TriangulatedK0.of ((toPerfect X).obj E) := sorry

end AlgebraicGeometry.Scheme.VectorBundleK0
