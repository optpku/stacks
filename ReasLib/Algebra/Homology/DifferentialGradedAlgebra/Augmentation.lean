module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.DegreeZero

/-!
# Augmentations of chain differential graded algebras

An augmentation to an ordinary commutative algebra is represented by a chain-DGA homomorphism
to its canonical degree-zero model.  The source-facing structure retains the elementary chain-map
description, while `Augmentation.toChainHom` exposes the reusable categorical owner.  Its map on
zeroth homology is then obtained functorially and evaluated through the canonical degree-zero
homology equivalence.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ChainDGAlgebra

variable {R : Type u} [CommRing R]

/-- An augmentation of a chain DGA to an ordinary algebra in degree zero. -/
@[stacks 09PN "infrastructure: augmentation to an ordinary algebra"]
structure Augmentation (A : ChainDGAlgebra.{u, v} R)
    (S : Type v) [CommRing S] [Algebra R S] where
  /-- The underlying chain map to the single-term complex. -/
  toChainMap : A.toChainComplex ⟶ degreeZeroComplex R S
  /-- The degree-zero component preserves the unit. -/
  map_one : (degreeZeroIso R S).hom (toChainMap.f 0 A.one) = 1
  /-- The degree-zero component preserves multiplication. -/
  map_mul (x y : A.X 0) :
    (degreeZeroIso R S).hom (toChainMap.f 0 (A.mul 0 0 x y)) =
      (degreeZeroIso R S).hom (toChainMap.f 0 x) *
        (degreeZeroIso R S).hom (toChainMap.f 0 y)

namespace Augmentation

variable {A B : ChainDGAlgebra.{u, v} R}
variable {S : Type v} [CommRing S] [Algebra R S]

/-- Precomposing an augmentation with a chain-DGA homomorphism preserves the unit. -/
theorem comp_map_one (augmentation : Augmentation B S) (f : Hom A B) :
    (degreeZeroIso R S).hom
        ((f.toChainMap ≫ augmentation.toChainMap).f 0 A.one) = 1 := sorry

/-- Precomposing an augmentation with a chain-DGA homomorphism preserves multiplication in
degree zero. -/
theorem comp_map_mul (augmentation : Augmentation B S) (f : Hom A B)
    (x y : A.X 0) :
    (degreeZeroIso R S).hom
        ((f.toChainMap ≫ augmentation.toChainMap).f 0 (A.mul 0 0 x y)) =
      (degreeZeroIso R S).hom
          ((f.toChainMap ≫ augmentation.toChainMap).f 0 x) *
        (degreeZeroIso R S).hom
          ((f.toChainMap ≫ augmentation.toChainMap).f 0 y) := sorry

/-- Pull an augmentation back along a chain-DGA homomorphism. -/
def comp (augmentation : Augmentation B S) (f : Hom A B) : Augmentation A S where
  toChainMap := f.toChainMap ≫ augmentation.toChainMap
  map_one := augmentation.comp_map_one f
  map_mul := augmentation.comp_map_mul f

/-- The chain map of a pulled-back augmentation is the composite chain map. -/
@[simp]
theorem comp_toChainMap (augmentation : Augmentation B S) (f : Hom A B) :
    (augmentation.comp f).toChainMap =
      f.toChainMap ≫ augmentation.toChainMap := sorry

/-- The chain map of an augmentation preserves the chain-DGA unit. -/
theorem toChainHom_map_one (augmentation : Augmentation A S) :
    augmentation.toChainMap.f 0 A.one = (ofAlgebra R S).one := sorry

/-- The chain map of an augmentation preserves homogeneous multiplication in every degree. -/
theorem toChainHom_map_mul (augmentation : Augmentation A S) (n m : ℤ)
    (x : A.X n) (y : A.X m) :
    augmentation.toChainMap.f (n + m) (A.mul n m x y) =
      (ofAlgebra R S).mul n m
        (augmentation.toChainMap.f n x) (augmentation.toChainMap.f m y) := sorry

/-- An augmentation as a chain-DGA homomorphism to the ordinary algebra in degree zero. -/
@[stacks 09PN "infrastructure: augmentation as a chain-DGA homomorphism"]
noncomputable def toChainHom (augmentation : Augmentation A S) :
    Hom A (ofAlgebra R S) where
  toChainMap := augmentation.toChainMap
  map_one := augmentation.toChainHom_map_one
  map_mul := augmentation.toChainHom_map_mul

/-- The underlying chain map of the chain-DGA augmentation is the original augmentation map. -/
@[simp] theorem toChainHom_toChainMap (augmentation : Augmentation A S) :
    augmentation.toChainHom.toChainMap = augmentation.toChainMap := sorry

/-- The chain-DGA augmentation acts degreewise by the original chain map. -/
@[simp] theorem toChainHom_apply (augmentation : Augmentation A S)
    (n : ℤ) (x : A.X n) :
    augmentation.toChainHom n x = augmentation.toChainMap.f n x := sorry

variable [A.IsStrictlyCommutative]

/-- The canonical algebra homomorphism on zeroth homology induced functorially by an
augmentation. -/
noncomputable def homologyZeroMap (augmentation : Augmentation A S) :
    A.homologyZero →ₐ[R] S :=
  (homologyZeroEquiv R S).toAlgHom.comp augmentation.toChainHom.homologyZeroMap

/-- Pulling back an augmentation composes its map on zeroth homology with the map induced by the
chain-DGA homomorphism. -/
@[simp]
theorem comp_homologyZeroMap [B.IsStrictlyCommutative]
    (augmentation : Augmentation B S) (f : Hom A B) :
    (augmentation.comp f).homologyZeroMap =
      augmentation.homologyZeroMap.comp f.homologyZeroMap := sorry

/-- On a cycle class, the canonical zeroth-homology map is the degree-zero component of the
augmentation. -/
@[simp] theorem homologyZeroMap_homologyπ (augmentation : Augmentation A S)
    (x : A.cycles 0) :
    augmentation.homologyZeroMap (A.homologyπ 0 x) =
      (degreeZeroIso R S).hom (augmentation.toChainMap.f 0 (A.iCycles 0 x)) := sorry

/-- A quasi-isomorphic augmentation induces a bijection on canonical zeroth homology. -/
theorem homologyZeroMap_bijective (augmentation : Augmentation A S)
    [QuasiIso augmentation.toChainMap] :
    Function.Bijective augmentation.homologyZeroMap := sorry

end Augmentation

namespace Hom

variable {A B : ChainDGAlgebra.{u, v} R}
variable [A.IsStrictlyCommutative] [B.IsStrictlyCommutative]
variable {S T : Type v} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- A chain-DGA homomorphism over an algebra map commutes on zeroth homology with the source and
target augmentations. -/
def CommutesOnH0Over (f : Hom A B) (sigma : S →ₐ[R] T)
    (augmentationA : Augmentation A S) (augmentationB : Augmentation B T) : Prop :=
  augmentationB.homologyZeroMap.comp f.homologyZeroMap =
    sigma.comp augmentationA.homologyZeroMap

/-- Commutation over an algebra map is the corresponding pointwise square on zeroth homology. -/
theorem commutesOnH0Over_iff (f : Hom A B) (sigma : S →ₐ[R] T)
    (augmentationA : Augmentation A S) (augmentationB : Augmentation B T) :
    f.CommutesOnH0Over sigma augmentationA augmentationB ↔
      ∀ x : A.homologyZero,
        augmentationB.homologyZeroMap (f.homologyZeroMap x) =
          sigma (augmentationA.homologyZeroMap x) := sorry

/-- The identity chain-DGA map commutes over the identity algebra map with any augmentation. -/
theorem commutesOnH0Over_id (augmentation : Augmentation A S) :
    (Hom.id A).CommutesOnH0Over (AlgHom.id R S) augmentation augmentation := sorry

/-- Commutation of augmentation squares is preserved by composition. -/
theorem commutesOnH0Over_comp
    {C : ChainDGAlgebra.{u, v} R} [C.IsStrictlyCommutative]
    {U : Type v} [CommRing U] [Algebra R U]
    {augmentationA : Augmentation A S} {augmentationB : Augmentation B T}
    {augmentationC : Augmentation C U}
    {f : Hom A B} {g : Hom B C} {sigma : S →ₐ[R] T} {tau : T →ₐ[R] U}
    (hf : f.CommutesOnH0Over sigma augmentationA augmentationB)
    (hg : g.CommutesOnH0Over tau augmentationB augmentationC) :
    (Hom.comp g f).CommutesOnH0Over (tau.comp sigma) augmentationA augmentationC := sorry

/-- A chain-DGA homomorphism commutes on zeroth homology with augmentations to the same target. -/
def CommutesOnH0 (f : Hom A B) (augmentationA : Augmentation A S)
    (augmentationB : Augmentation B S) : Prop :=
  f.CommutesOnH0Over (AlgHom.id R S) augmentationA augmentationB

/-- Commutation on zeroth homology is the pointwise commutative-triangle identity. -/
theorem commutesOnH0_iff (f : Hom A B) (augmentationA : Augmentation A S)
    (augmentationB : Augmentation B S) :
    f.CommutesOnH0 augmentationA augmentationB ↔
      ∀ x : A.homologyZero,
        augmentationB.homologyZeroMap (f.homologyZeroMap x) =
          augmentationA.homologyZeroMap x := sorry

end Hom

namespace Augmentation

variable {A B C : ChainDGAlgebra.{u, v} R}
variable [A.IsStrictlyCommutative] [B.IsStrictlyCommutative] [C.IsStrictlyCommutative]
variable {S T U : Type v}
variable [CommRing S] [CommRing T] [CommRing U]
variable [Algebra R S] [Algebra R T] [Algebra R U]

/-- A morphism of augmented chain DGAs, allowing the ordinary target algebra to vary. The two
maps are explicit data; compatibility is imposed on canonical zeroth homology. -/
structure Hom (augmentationA : Augmentation A S) (augmentationB : Augmentation B T) where
  /-- The map between the source chain DGAs. -/
  toChainHom : ChainDGAlgebra.Hom A B
  /-- The map between the ordinary augmentation targets. -/
  toAlgHom : S →ₐ[R] T
  /-- The induced square on canonical zeroth homology commutes. -/
  commutesOnH0 :
    toChainHom.CommutesOnH0Over toAlgHom augmentationA augmentationB

namespace Hom

variable {augmentationA : Augmentation A S}
variable {augmentationB : Augmentation B T}
variable {augmentationC : Augmentation C U}

/-- Morphisms of augmented chain DGAs are determined by their two explicit maps. -/
@[ext]
theorem ext {f g : Augmentation.Hom augmentationA augmentationB}
    (h_chain : f.toChainHom = g.toChainHom) (h_target : f.toAlgHom = g.toAlgHom) :
    f = g := sorry

/-- The identity morphism of an augmented chain DGA. -/
def id (augmentation : Augmentation A S) : Augmentation.Hom augmentation augmentation where
  toChainHom := ChainDGAlgebra.Hom.id A
  toAlgHom := AlgHom.id R S
  commutesOnH0 := ChainDGAlgebra.Hom.commutesOnH0Over_id augmentation

/-- The chain-DGA map underlying the identity augmented morphism is the identity. -/
@[simp]
theorem id_toChainHom (augmentation : Augmentation A S) :
    (id augmentation).toChainHom = ChainDGAlgebra.Hom.id A := sorry

/-- The target-algebra map underlying the identity augmented morphism is the identity. -/
@[simp]
theorem id_toAlgHom (augmentation : Augmentation A S) :
    (id augmentation).toAlgHom = AlgHom.id R S := sorry

/-- Composition of morphisms of augmented chain DGAs. -/
def comp (g : Augmentation.Hom augmentationB augmentationC)
    (f : Augmentation.Hom augmentationA augmentationB) :
    Augmentation.Hom augmentationA augmentationC where
  toChainHom := ChainDGAlgebra.Hom.comp g.toChainHom f.toChainHom
  toAlgHom := g.toAlgHom.comp f.toAlgHom
  commutesOnH0 := ChainDGAlgebra.Hom.commutesOnH0Over_comp
    f.commutesOnH0 g.commutesOnH0

/-- The chain-DGA map underlying a composite augmented morphism is the composite map. -/
@[simp]
theorem comp_toChainHom (g : Augmentation.Hom augmentationB augmentationC)
    (f : Augmentation.Hom augmentationA augmentationB) :
    (comp g f).toChainHom = ChainDGAlgebra.Hom.comp g.toChainHom f.toChainHom := sorry

/-- The target-algebra map underlying a composite augmented morphism is the composite map. -/
@[simp]
theorem comp_toAlgHom (g : Augmentation.Hom augmentationB augmentationC)
    (f : Augmentation.Hom augmentationA augmentationB) :
    (comp g f).toAlgHom = g.toAlgHom.comp f.toAlgHom := sorry

/-- Composing with the identity on the source leaves an augmented morphism unchanged. -/
@[simp]
theorem id_comp (f : Augmentation.Hom augmentationA augmentationB) :
    comp f (id augmentationA) = f := sorry

/-- Composing with the identity on the target leaves an augmented morphism unchanged. -/
@[simp]
theorem comp_id (f : Augmentation.Hom augmentationA augmentationB) :
    comp (id augmentationB) f = f := sorry

/-- Composition of augmented chain-DGA morphisms is associative. -/
theorem assoc
    {D : ChainDGAlgebra.{u, v} R} [D.IsStrictlyCommutative]
    {V : Type v} [CommRing V] [Algebra R V]
    {augmentationD : Augmentation D V}
    (h : Augmentation.Hom augmentationC augmentationD)
    (g : Augmentation.Hom augmentationB augmentationC)
    (f : Augmentation.Hom augmentationA augmentationB) :
    comp h (comp g f) = comp (comp h g) f := sorry

end Hom

end Augmentation

end ChainDGAlgebra
