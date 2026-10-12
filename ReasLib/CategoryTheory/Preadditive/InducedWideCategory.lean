/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Preadditive induced wide categories

This file packages morphism properties that are closed under the additive operations of a
preadditive category. Such a property induces a preadditive structure on the corresponding
wide category, and its forgetful functor is additive.
-/

@[expose] public section

namespace CategoryTheory

universe v v' u₁ u₂

namespace MorphismProperty

variable {D : Type u₂} [Category.{v} D] [Preadditive D]

/-- A multiplicative morphism property is preadditive when it contains zero morphisms and is
closed under addition and negation. -/
class IsPreadditive (W : MorphismProperty D) : Prop extends W.IsMultiplicative where
  /-- Every zero morphism belongs to the property. -/
  zero_mem (W) (X Y : D) : W (0 : X ⟶ Y)
  /-- The property is closed under addition of parallel morphisms. -/
  add_mem (W) {X Y : D} {f g : X ⟶ Y} : W f → W g → W (f + g)
  /-- The property is closed under negation. -/
  neg_mem (W) {X Y : D} {f : X ⟶ Y} : W f → W (-f)

export IsPreadditive (zero_mem add_mem neg_mem)

namespace IsPreadditive

/-- The maximal morphism property is preadditive. -/
instance top : IsPreadditive (⊤ : MorphismProperty D) := sorry

/-- The intersection of two preadditive morphism properties is preadditive. -/
instance inf {W₁ W₂ : MorphismProperty D} [W₁.IsPreadditive] [W₂.IsPreadditive] :
    IsPreadditive (W₁ ⊓ W₂) := sorry

/-- The inverse image of a preadditive morphism property under an additive functor is
preadditive. -/
instance inverseImage {C : Type u₁} [Category.{v'} C] [Preadditive C]
    (W : MorphismProperty D) [W.IsPreadditive] (G : C ⥤ D) [G.Additive] :
    (W.inverseImage G).IsPreadditive := sorry

end IsPreadditive

/-- A preadditive morphism property is closed under subtraction. -/
theorem sub_mem (W : MorphismProperty D) [W.IsPreadditive]
    {X Y : D} {f g : X ⟶ Y} (hf : W f) (hg : W g) : W (f - g) := sorry

/-- A preadditive morphism property is closed under natural-number scalar multiplication. -/
theorem nsmul_mem (W : MorphismProperty D) [W.IsPreadditive]
    {X Y : D} {f : X ⟶ Y} (hf : W f) (n : ℕ) : W (n • f) := sorry

/-- A preadditive morphism property is closed under integer scalar multiplication. -/
theorem zsmul_mem (W : MorphismProperty D) [W.IsPreadditive]
    {X Y : D} {f : X ⟶ Y} (hf : W f) (n : ℤ) : W (n • f) := sorry

end MorphismProperty

namespace InducedWideCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v} D] [Preadditive D]
variable {F : C → D} {W : MorphismProperty D} [W.IsPreadditive]
variable {X Y : InducedWideCategory D F W}

/-- An induced wide category for a preadditive morphism property inherits zero morphisms. -/
instance (priority := 900) instHasZeroMorphisms :
    Limits.HasZeroMorphisms (InducedWideCategory D F W) where
  zero X Y := ⟨(0 : F X ⟶ F Y), W.zero_mem _ _⟩
  comp_zero := sorry
  zero_comp := sorry

/-- The underlying ambient morphism of a zero morphism is zero. -/
@[simp]
theorem zero_hom : (0 : X ⟶ Y).hom = (0 : F X ⟶ F Y) := sorry

/-- Addition of morphisms in an induced wide category is inherited from the ambient category. -/
instance homAdd : Add (X ⟶ Y) where
  add f g := ⟨f.hom + g.hom, W.add_mem f.property g.property⟩

/-- Negation of morphisms in an induced wide category is inherited from the ambient category. -/
instance homNeg : Neg (X ⟶ Y) where
  neg f := ⟨-f.hom, W.neg_mem f.property⟩

/-- Subtraction of morphisms in an induced wide category is inherited from the ambient category. -/
instance homSub : Sub (X ⟶ Y) where
  sub f g := ⟨f.hom - g.hom, W.sub_mem f.property g.property⟩

/-- Natural-number scalar multiplication in an induced wide category is inherited from the
ambient category. -/
instance homNatSMul : SMul ℕ (X ⟶ Y) where
  smul n f := ⟨n • f.hom, W.nsmul_mem f.property n⟩

/-- Integer scalar multiplication in an induced wide category is inherited from the ambient
category. -/
instance homIntSMul : SMul ℤ (X ⟶ Y) where
  smul n f := ⟨n • f.hom, W.zsmul_mem f.property n⟩

/-- The underlying ambient morphism of a sum is the sum of the underlying morphisms. -/
@[simp]
theorem add_hom (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom := sorry

/-- The underlying ambient morphism of a negation is the negated underlying morphism. -/
@[simp]
theorem neg_hom (f : X ⟶ Y) : (-f).hom = -f.hom := sorry

/-- The underlying ambient morphism of a difference is the difference of the underlying
morphisms. -/
@[simp]
theorem sub_hom (f g : X ⟶ Y) : (f - g).hom = f.hom - g.hom := sorry

/-- The underlying ambient morphism of a natural-number multiple is the corresponding multiple. -/
@[simp]
theorem nsmul_hom (n : ℕ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := sorry

/-- The underlying ambient morphism of an integer multiple is the corresponding multiple. -/
@[simp]
theorem zsmul_hom (n : ℤ) (f : X ⟶ Y) : (n • f).hom = n • f.hom := sorry

/-- The map from an induced-wide hom type to its ambient hom type is injective. -/
theorem hom_injective :
    Function.Injective
      (InducedWideCategory.Hom.hom : (X ⟶ Y) → (F X ⟶ F Y)) := sorry

/-- Morphisms in an induced wide category form an additive commutative group. -/
instance homAddCommGroup : AddCommGroup (X ⟶ Y) :=
  Function.Injective.addCommGroup InducedWideCategory.Hom.hom hom_injective
    zero_hom (fun _ _ ↦ add_hom _ _) (fun _ ↦ neg_hom _)
      (fun _ _ ↦ sub_hom _ _) (fun _ _ ↦ nsmul_hom _ _)
        (fun _ _ ↦ zsmul_hom _ _)

/-- An induced wide category for a preadditive morphism property inherits the ambient
preadditive structure. -/
instance instPreadditive : Preadditive (InducedWideCategory D F W) where
  homGroup := fun _ _ ↦ homAddCommGroup
  add_comp := sorry
  comp_add := sorry

/-- The forgetful functor from a preadditive induced wide category is additive. -/
instance wideInducedFunctorAdditive : (wideInducedFunctor F W).Additive := sorry

end InducedWideCategory

namespace WideSubcategory

variable {D : Type u₂} [Category.{v} D] [Preadditive D]
variable (W : MorphismProperty D) [W.IsPreadditive]

/-- A wide subcategory defined by a preadditive morphism property inherits zero morphisms. -/
instance (priority := 900) instHasZeroMorphisms :
    Limits.HasZeroMorphisms (WideSubcategory W) :=
  InducedWideCategory.instHasZeroMorphisms (F := WideSubcategory.obj) (W := W)

/-- A wide subcategory defined by a preadditive morphism property inherits the ambient
preadditive structure. -/
instance instPreadditive : Preadditive (WideSubcategory W) :=
  InducedWideCategory.instPreadditive (F := WideSubcategory.obj) (W := W)

/-- The inclusion of a wide subcategory defined by a preadditive morphism property is additive. -/
instance inclusionAdditive : (wideSubcategoryInclusion W).Additive :=
  InducedWideCategory.wideInducedFunctorAdditive

end WideSubcategory

end CategoryTheory
