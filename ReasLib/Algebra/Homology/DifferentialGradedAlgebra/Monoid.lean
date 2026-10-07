module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Mon
public import ReasLib.Algebra.Homology.ComplexShapeSigns
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Category
public import ReasLib.Algebra.Homology.HomologicalComplex.Monoidal.Component
import Mathlib.Tactic.CrossRefAttribute

/-!
# Chain differential graded algebras from monoid objects

A monoid object in integer-indexed chain complexes carries exactly the unit, homogeneous
multiplication, and coherence needed for a chain differential graded algebra. The tensor signs on
integer chain degrees are supplied by the lower `Algebra.Homology.ComplexShapeSigns` owner.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace ChainDGAlgebra

variable {R : Type u} [CommRing R]

/-- The degree-zero unit extracted from a monoid object in chain complexes. -/
@[stacks 0GZ4 "unit extracted from an integer chain-complex monoid"]
noncomputable def ofMonOne
    (A : Mon (ChainComplex (ModuleCat.{u} R) ℤ)) : A.X.X 0 :=
  (HomologicalComplex.Monoidal.unitHomComponent A.mon.one).hom (1 : R)

/-- The homogeneous multiplication extracted from a monoid object in chain complexes. -/
@[stacks 0GZ4 "multiplication extracted from an integer chain-complex monoid"]
noncomputable def ofMonMul
    (A : Mon (ChainComplex (ModuleCat.{u} R) ℤ)) (n m : ℤ) :
    A.X.X n →ₗ[R] A.X.X m →ₗ[R] A.X.X (n + m) :=
  _root_.TensorProduct.curry
    (HomologicalComplex.Monoidal.tensorHomComponent A.mon.mul n m).hom

/-- The multiplication extracted from a chain-complex monoid is associative. -/
theorem ofMon_mul_assoc
    (A : Mon (ChainComplex (ModuleCat.{u} R) ℤ)) (i j k : ℤ)
    (a : A.X.X i) (b : A.X.X j) (c : A.X.X k) :
    cast (congrArg (fun n : ℤ ↦ (A.X.X n : Type u)) (add_assoc i j k))
        (ofMonMul A (i + j) k (ofMonMul A i j a b) c) =
      ofMonMul A i (j + k) a (ofMonMul A j k b c) := sorry

/-- The unit extracted from a chain-complex monoid acts on the left. -/
theorem ofMon_one_mul
    (A : Mon (ChainComplex (ModuleCat.{u} R) ℤ)) (n : ℤ) (a : A.X.X n) :
    cast (congrArg (fun i : ℤ ↦ (A.X.X i : Type u)) (zero_add n))
        (ofMonMul A 0 n (ofMonOne A) a) = a := sorry

/-- The unit extracted from a chain-complex monoid acts on the right. -/
theorem ofMon_mul_one
    (A : Mon (ChainComplex (ModuleCat.{u} R) ℤ)) (n : ℤ) (a : A.X.X n) :
    cast (congrArg (fun i : ℤ ↦ (A.X.X i : Type u)) (add_zero n))
        (ofMonMul A n 0 a (ofMonOne A)) = a := sorry

/-- The homogeneous multiplication extracted from a chain-complex monoid satisfies the chain
Leibniz rule. -/
theorem ofMon_leibniz
    (A : Mon (ChainComplex (ModuleCat.{u} R) ℤ)) (n m : ℤ)
    (a : A.X.X n) (b : A.X.X m) :
    A.X.d (n + m) (n + m - 1) (ofMonMul A n m a b) =
      cast (congrArg (fun i : ℤ ↦ (A.X.X i : Type u))
          (ChainDGAlgebra.leftLeibnizIndex n m))
          (ofMonMul A (n - 1) m (A.X.d n (n - 1) a) b) +
        n.negOnePow •
          cast (congrArg (fun i : ℤ ↦ (A.X.X i : Type u))
            (ChainDGAlgebra.rightLeibnizIndex n m))
            (ofMonMul A n (m - 1) a (A.X.d m (m - 1) b)) := sorry

/-- Recover a chain differential graded algebra from a monoid object in integer-indexed chain
complexes. -/
@[stacks 0GZ4 "chain DGA recovered from an integer chain-complex monoid"]
noncomputable def ofMon
    (A : Mon (ChainComplex (ModuleCat.{u} R) ℤ)) : ChainDGAlgebra R where
  toChainComplex := A.X
  mul := ofMonMul A
  one := ofMonOne A
  mul_assoc := ofMon_mul_assoc A
  one_mul := ofMon_one_mul A
  mul_one := ofMon_mul_one A
  leibniz := ofMon_leibniz A

/-- A monoid morphism preserves the extracted degree-zero unit. -/
theorem ofMonMap_one
    {A B : Mon (ChainComplex (ModuleCat.{u} R) ℤ)} (f : A ⟶ B) :
    f.hom.f 0 (ofMonOne A) = ofMonOne B := sorry

/-- A monoid morphism preserves the extracted homogeneous multiplication. -/
theorem ofMonMap_mul
    {A B : Mon (ChainComplex (ModuleCat.{u} R) ℤ)} (f : A ⟶ B)
    (n m : ℤ) (a : A.X.X n) (b : A.X.X m) :
    f.hom.f (n + m) (ofMonMul A n m a b) =
      ofMonMul B n m (f.hom.f n a) (f.hom.f m b) := sorry

/-- A monoid morphism of integer chain complexes as a morphism of the recovered chain DGAs. -/
@[stacks 0GZ4 "chain-DGA map recovered from a chain-complex monoid morphism"]
noncomputable def ofMonMap
    {A B : Mon (ChainComplex (ModuleCat.{u} R) ℤ)} (f : A ⟶ B) :
    ofMon A ⟶ ofMon B where
  toChainMap := f.hom
  map_one := ofMonMap_one f
  map_mul := ofMonMap_mul f

/-- Recovery from chain-complex monoids preserves identity morphisms. -/
@[simp]
theorem ofMonMap_id (A : Mon (ChainComplex (ModuleCat.{u} R) ℤ)) :
    ofMonMap (R := R) (𝟙 A) = 𝟙 (ofMon A) := sorry

/-- Recovery from chain-complex monoids preserves composition. -/
@[simp]
theorem ofMonMap_comp
    {A B C : Mon (ChainComplex (ModuleCat.{u} R) ℤ)}
    (f : A ⟶ B) (g : B ⟶ C) :
    ofMonMap (f ≫ g) = ofMonMap f ≫ ofMonMap g := sorry

/-- The functor recovering chain differential graded algebras from monoid objects in
integer-indexed chain complexes. -/
@[stacks 0GZ4 "chain-DGA recovery functor"]
noncomputable def ofMonFunctor (R : Type u) [CommRing R] :
    Mon (ChainComplex (ModuleCat.{u} R) ℤ) ⥤ ChainDGAlgebra R where
  obj := ofMon
  map := ofMonMap
  map_id := ofMonMap_id
  map_comp := ofMonMap_comp

/-- The underlying chain complex of a recovered DGA is the carrier of the monoid object. -/
@[simp]
theorem ofMon_toChainComplex
    (A : Mon (ChainComplex (ModuleCat.{u} R) ℤ)) :
    (ofMon A).toChainComplex = A.X := sorry

/-- The underlying chain map of a recovered DGA morphism is the monoid morphism carrier. -/
@[simp]
theorem ofMonMap_toChainMap
    {A B : Mon (ChainComplex (ModuleCat.{u} R) ℤ)} (f : A ⟶ B) :
    (ofMonMap f).toChainMap = f.hom := sorry

/-- The recovery functor acts on objects by `ofMon`. -/
@[simp]
theorem ofMonFunctor_obj
    (A : Mon (ChainComplex (ModuleCat.{u} R) ℤ)) :
    (ofMonFunctor R).obj A = ofMon A := sorry

/-- The recovery functor acts on morphisms by `ofMonMap`. -/
@[simp]
theorem ofMonFunctor_map
    {A B : Mon (ChainComplex (ModuleCat.{u} R) ℤ)} (f : A ⟶ B) :
    (ofMonFunctor R).map f = ofMonMap f := sorry

#synth MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℤ)

-- The carrier, unit, multiplication, and maps are explicit. Any `sorryAx` dependency is confined
-- to proposition-valued monoid laws, chain compatibility, and functoriality fields.

end ChainDGAlgebra
