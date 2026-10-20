module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Ring
public import ReasLib.AlgebraicGeometry.Scheme.K0.Support

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0WithSupport

/-- Derived tensoring two supported perfect objects preserves the support condition. -/
theorem tensorObj_isSupportedOn (X : Scheme.{u}) (T : Set X)
    (K L : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    RingedSpace.ModuleDerived.IsSupportedOn
      ((DerivedCategory.DerivedTensor.Right.functor L.obj).obj K.obj) T := sorry

/-- The derived tensor product of two supported perfect objects. -/
noncomputable def tensorObj (X : Scheme.{u}) (T : Set X)
    (K L : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    RingedSpace.ModuleDerived.PerfectSupportedOn T :=
  let P := K0.tensorObj X
    (⟨K.obj, K.property.1⟩ :
      RingedSpace.ModuleDerived.Perfect)
    (⟨L.obj, L.property.1⟩ :
      RingedSpace.ModuleDerived.Perfect)
  ⟨P.obj, ⟨P.property, tensorObj_isSupportedOn X T K L⟩⟩

/-- The underlying derived object of `K0WithSupport.tensorObj` is the derived tensor product. -/
theorem tensorObj_obj (X : Scheme.{u}) (T : Set X)
    (K L : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    (tensorObj X T K L).obj =
      (DerivedCategory.DerivedTensor.Right.functor L.obj).obj K.obj := sorry

/-- Tensoring with a fixed supported perfect object kills the triangle relations in the other
variable. -/
theorem relations_le_ker_mulOf (X : Scheme.{u}) (T : Set X)
    (K : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    TriangulatedK0.relations
        (RingedSpace.ModuleDerived.PerfectSupportedOn T) ≤
      (FreeAbelianGroup.lift fun L :
          RingedSpace.ModuleDerived.PerfectSupportedOn T ↦
        TriangulatedK0.of (tensorObj X T K L)).ker := sorry

/-- Multiplication by the class of a fixed supported perfect complex. -/
noncomputable def mulOf (X : Scheme.{u}) (T : Set X)
    (K : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    K0WithSupport X T →+ K0WithSupport X T :=
  TriangulatedK0.lift (fun L ↦ TriangulatedK0.of (tensorObj X T K L))
    (relations_le_ker_mulOf X T K)

/-- `mulOf` sends a supported-perfect generator to its derived-tensor class. -/
theorem mulOf_of (X : Scheme.{u}) (T : Set X)
    (K L : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    mulOf X T K (TriangulatedK0.of L) =
      TriangulatedK0.of (tensorObj X T K L) := sorry

/-- Supported-perfect classes defining `mulOf` kill the triangle relations. -/
theorem relations_le_ker_mul (X : Scheme.{u}) (T : Set X) :
    TriangulatedK0.relations
        (RingedSpace.ModuleDerived.PerfectSupportedOn T) ≤
      (FreeAbelianGroup.lift fun K :
          RingedSpace.ModuleDerived.PerfectSupportedOn T ↦ mulOf X T K).ker := sorry

/-- The tensor-induced biadditive multiplication on supported perfect `K₀`. -/
noncomputable def mul (X : Scheme.{u}) (T : Set X) :
    K0WithSupport X T →+ K0WithSupport X T →+ K0WithSupport X T :=
  TriangulatedK0.lift (mulOf X T) (relations_le_ker_mul X T)

/-- Multiplication of supported-perfect generators is represented by derived tensor product. -/
theorem mul_of (X : Scheme.{u}) (T : Set X)
    (K L : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    mul X T (TriangulatedK0.of K) (TriangulatedK0.of L) =
      TriangulatedK0.of (tensorObj X T K L) := sorry

/-- Multiplication on supported perfect `K₀` is the tensor-induced biadditive operation. -/
noncomputable instance instMul (X : Scheme.{u}) (T : Set X) :
    Mul (K0WithSupport X T) :=
  ⟨fun x y ↦ mul X T x y⟩

/-- Derived tensor multiplication on supported perfect `K₀` is associative. -/
theorem mul_assoc_axiom (X : Scheme.{u}) (T : Set X)
    (a b c : K0WithSupport X T) : a * b * c = a * (b * c) := sorry

/-- Derived tensor multiplication on supported perfect `K₀` is commutative. -/
theorem mul_comm_axiom (X : Scheme.{u}) (T : Set X)
    (a b : K0WithSupport X T) : a * b = b * a := sorry

/-- Derived tensor multiplication distributes over addition on the right. -/
theorem mul_add_axiom (X : Scheme.{u}) (T : Set X)
    (a b c : K0WithSupport X T) : a * (b + c) = a * b + a * c := sorry

/-- Derived tensor multiplication distributes over addition on the left. -/
theorem add_mul_axiom (X : Scheme.{u}) (T : Set X)
    (a b c : K0WithSupport X T) : (a + b) * c = a * c + b * c := sorry

/-- Zero is absorbing on the left for derived tensor multiplication. -/
theorem zero_mul_axiom (X : Scheme.{u}) (T : Set X) (a : K0WithSupport X T) :
    0 * a = 0 := sorry

/-- Zero is absorbing on the right for derived tensor multiplication. -/
theorem mul_zero_axiom (X : Scheme.{u}) (T : Set X) (a : K0WithSupport X T) :
    a * 0 = 0 := sorry

/-- The canonical nonunital commutative-ring structure on supported perfect `K₀`. -/
noncomputable instance instNonUnitalCommRing (X : Scheme.{u}) (T : Set X) :
    NonUnitalCommRing (K0WithSupport X T) where
  toNonUnitalRing := {
    toAddCommGroup := inferInstance
    mul := fun a b ↦ mul X T a b
    mul_assoc := mul_assoc_axiom X T
    left_distrib := mul_add_axiom X T
    right_distrib := add_mul_axiom X T
    zero_mul := zero_mul_axiom X T
    mul_zero := mul_zero_axiom X T }
  mul_comm := mul_comm_axiom X T

/-- Forgetting support preserves tensor-induced multiplication. -/
theorem forget_map_mul (X : Scheme.{u}) (T : Set X)
    (a b : K0WithSupport X T) :
    forget X T (a * b) = forget X T a * forget X T b := sorry

/-- The comparison from supported perfect `K₀` to ordinary perfect `K₀` as a nonunital ring
homomorphism. -/
noncomputable def toK0NonUnitalRingHom (X : Scheme.{u}) (T : Set X) :
    K0WithSupport X T →ₙ+* K0 X where
  toFun := forget X T
  map_mul' := forget_map_mul X T
  map_zero' := (forget X T).map_zero
  map_add' := (forget X T).map_add

/-- The nonunital ring comparison sends a supported-perfect generator to its ordinary perfect
class. -/
theorem toK0NonUnitalRingHom_of (X : Scheme.{u}) (T : Set X)
    (K : RingedSpace.ModuleDerived.PerfectSupportedOn T) :
    toK0NonUnitalRingHom X T (TriangulatedK0.of K) =
      TriangulatedK0.of
        (⟨K.obj, K.property.1⟩ :
          RingedSpace.ModuleDerived.Perfect) := sorry

end AlgebraicGeometry.Scheme.K0WithSupport
