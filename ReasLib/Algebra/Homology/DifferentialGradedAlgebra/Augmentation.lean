/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.DegreeZero

/-!
# Augmentations of chain differential graded algebras

An augmentation to an ordinary commutative algebra retains the elementary chain-map description
and preserves multiplication in degree zero.  For a nonnegative source,
`Augmentation.toChainHom` exposes the corresponding chain-DGA homomorphism.  In arbitrary integer
degrees, the map on zeroth homology is constructed directly from the original chain map.
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
        ((f.toChainMap ≫ augmentation.toChainMap).f 0 A.one) = 1 := by
  change (degreeZeroIso R S).hom
    (augmentation.toChainMap.f 0 (f.toChainMap.f 0 A.one)) = 1
  rw [f.map_one]
  exact augmentation.map_one

/-- Precomposing an augmentation with a chain-DGA homomorphism preserves multiplication in
degree zero. -/
theorem comp_map_mul (augmentation : Augmentation B S) (f : Hom A B)
    (x y : A.X 0) :
    (degreeZeroIso R S).hom
        ((f.toChainMap ≫ augmentation.toChainMap).f 0 (A.mul 0 0 x y)) =
      (degreeZeroIso R S).hom
          ((f.toChainMap ≫ augmentation.toChainMap).f 0 x) *
        (degreeZeroIso R S).hom
          ((f.toChainMap ≫ augmentation.toChainMap).f 0 y) := by
  change (degreeZeroIso R S).hom
      (augmentation.toChainMap.f 0 (f.toChainMap.f 0 (A.mul 0 0 x y))) =
    (degreeZeroIso R S).hom (augmentation.toChainMap.f 0 (f.toChainMap.f 0 x)) *
      (degreeZeroIso R S).hom (augmentation.toChainMap.f 0 (f.toChainMap.f 0 y))
  exact (congrArg
    (fun z : B.X 0 ↦ (degreeZeroIso R S).hom (augmentation.toChainMap.f 0 z))
    (f.map_mul 0 0 x y)).trans (augmentation.map_mul _ _)

/-- Pull an augmentation back along a chain-DGA homomorphism. -/
def comp (augmentation : Augmentation B S) (f : Hom A B) : Augmentation A S where
  toChainMap := f.toChainMap ≫ augmentation.toChainMap
  map_one := augmentation.comp_map_one f
  map_mul := augmentation.comp_map_mul f

/-- The chain map of a pulled-back augmentation is the composite chain map. -/
@[simp]
theorem comp_toChainMap (augmentation : Augmentation B S) (f : Hom A B) :
    (augmentation.comp f).toChainMap =
      f.toChainMap ≫ augmentation.toChainMap := rfl

/-- The chain map of an augmentation preserves the chain-DGA unit. -/
theorem toChainHom_map_one (augmentation : Augmentation A S) :
    augmentation.toChainMap.f 0 A.one = (ofAlgebra R S).one := by
  change augmentation.toChainMap.f 0 A.one = (degreeZeroIso R S).inv (1 : S)
  rw [← augmentation.map_one]
  exact (ConcreteCategory.congr_hom (degreeZeroIso R S).hom_inv_id _).symm

/-- For a nonnegative source, the chain map of an augmentation preserves homogeneous
multiplication in every degree. -/
theorem toChainHom_map_mul (augmentation : Augmentation A S) [A.IsNonnegative] (n m : ℤ)
    (x : A.X n) (y : A.X m) :
    augmentation.toChainMap.f (n + m) (A.mul n m x y) =
      (ofAlgebra R S).mul n m
        (augmentation.toChainMap.f n x) (augmentation.toChainMap.f m y) := by
  have hzero (i : ℤ) (hi : i < 0) : Subsingleton (A.X i) := by
    apply ModuleCat.subsingleton_of_isZero
    apply A.toChainComplex.isZero_X_of_isStrictlySupported
      ComplexShape.embeddingDownNatInt i
    intro j
    change (j : ℤ) ≠ i
    omega
  by_cases hnm : n + m = 0
  · by_cases hn : n = 0
    · have hm : m = 0 := by omega
      subst n
      subst m
      apply (ConcreteCategory.bijective_of_isIso (degreeZeroIso R S).hom).injective
      change (degreeZeroIso R S).hom
          (augmentation.toChainMap.f 0 (A.mul 0 0 x y)) =
        (degreeZeroIso R S).hom ((degreeZeroIso R S).inv
          ((degreeZeroIso R S).hom (augmentation.toChainMap.f 0 x) *
            (degreeZeroIso R S).hom (augmentation.toChainMap.f 0 y)))
      rw [Iso.inv_hom_id_apply]
      exact augmentation.map_mul x y
    · have hneg : n < 0 ∨ m < 0 := by omega
      rcases hneg with hneg | hneg
      · haveI := hzero n hneg
        have hx : x = 0 := Subsingleton.elim _ _
        subst x
        simp only [map_zero, LinearMap.zero_apply]
        exact (congrArg
          (fun z : (ofAlgebra R S).X m →ₗ[R] (ofAlgebra R S).X (n + m) ↦
            z (augmentation.toChainMap.f m y))
          ((ofAlgebra R S).mul n m).map_zero).symm
      · haveI := hzero m hneg
        have hy : y = 0 := Subsingleton.elim _ _
        subst y
        simp only [map_zero]
        exact ((ofAlgebra R S).mul n m (augmentation.toChainMap.f n x)).map_zero.symm
  · haveI := ModuleCat.subsingleton_of_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℤ) 0
        (ModuleCat.of R S) (n + m) hnm)
    exact Subsingleton.elim _ _

/-- An augmentation of a nonnegative source as a chain-DGA homomorphism to the ordinary algebra
in degree zero. -/
@[stacks 09PN "infrastructure: augmentation as a chain-DGA homomorphism"]
noncomputable def toChainHom (augmentation : Augmentation A S) [A.IsNonnegative] :
    Hom A (ofAlgebra R S) where
  toChainMap := augmentation.toChainMap
  map_one := augmentation.toChainHom_map_one
  map_mul := augmentation.toChainHom_map_mul

/-- The underlying chain map of the chain-DGA augmentation is the original augmentation map. -/
@[simp] theorem toChainHom_toChainMap (augmentation : Augmentation A S) [A.IsNonnegative] :
    augmentation.toChainHom.toChainMap = augmentation.toChainMap := rfl

/-- The chain-DGA augmentation acts degreewise by the original chain map. -/
@[simp] theorem toChainHom_apply (augmentation : Augmentation A S) [A.IsNonnegative]
    (n : ℤ) (x : A.X n) :
    augmentation.toChainHom n x = augmentation.toChainMap.f n x := rfl

variable [A.IsStrictlyCommutative]

/-- The canonical linear map on zeroth homology, using the original augmentation chain map.
The target comparison is Mathlib's homology isomorphism for a single-term complex. -/
noncomputable def homologyZeroLinearMap (augmentation : Augmentation A S) :
    A.homologyZero →ₗ[R] S :=
  (HomologicalComplex.homologyMap augmentation.toChainMap 0 ≫
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℤ) 0
      (ModuleCat.of R S)).hom).hom

/-- On a cycle class, the linear homology augmentation evaluates the original chain map. -/
theorem homologyZeroLinearMap_homologyπ (augmentation : Augmentation A S)
    (x : A.cycles 0) :
    augmentation.homologyZeroLinearMap (A.homologyπ 0 x) =
      (degreeZeroIso R S).hom (augmentation.toChainMap.f 0 (A.iCycles 0 x)) := by
  have h : A.homologyπ 0 ≫ HomologicalComplex.homologyMap augmentation.toChainMap 0 ≫
      (homologyZeroIso R S).hom =
      A.iCycles 0 ≫ augmentation.toChainMap.f 0 ≫ (degreeZeroIso R S).hom := by
    rw [HomologicalComplex.homologyπ_naturality_assoc]
    dsimp only [homologyZeroIso, degreeZeroIso]
    rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
      HomologicalComplex.singleObjCyclesSelfIso_hom, ← Category.assoc,
      HomologicalComplex.cyclesMap_i, Category.assoc]
  exact ConcreteCategory.congr_hom h x

/-- The linear homology augmentation preserves the unit class. -/
theorem homologyZeroLinearMap_one (augmentation : Augmentation A S) :
    augmentation.homologyZeroLinearMap 1 = 1 := by
  rw [A.homologyZero_one]
  change augmentation.homologyZeroLinearMap (A.homologyπ 0 A.oneCycle) = 1
  rw [homologyZeroLinearMap_homologyπ]
  have h_one : A.iCycles 0 A.oneCycle = A.one :=
    HomologicalComplex.i_cyclesMk A.toChainComplex A.one (-1)
      down_next_zero A.d_one_eq_zero
  rw [h_one]
  exact augmentation.map_one

/-- The linear homology augmentation preserves multiplication of degree-zero cycle classes. -/
theorem homologyZeroLinearMap_mul (augmentation : Augmentation A S)
    (x y : A.homologyZero) :
    augmentation.homologyZeroLinearMap (x * y) =
      augmentation.homologyZeroLinearMap x * augmentation.homologyZeroLinearMap y := by
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective (A.homologyπ 0)).mp inferInstance x
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (A.homologyπ 0)).mp inferInstance y
  rw [A.homologyZero_mul]
  trans augmentation.homologyZeroLinearMap (A.homologyπ 0 (A.cyclesMul 0 0 x y))
  · exact congrArg augmentation.homologyZeroLinearMap (A.homologyMul_class 0 0 x y)
  show augmentation.homologyZeroLinearMap (A.homologyπ 0 (A.cyclesMul 0 0 x y)) =
    augmentation.homologyZeroLinearMap (A.homologyπ 0 x) *
      augmentation.homologyZeroLinearMap (A.homologyπ 0 y)
  simp only [homologyZeroLinearMap_homologyπ]
  have h_mul : A.iCycles 0 (A.cyclesMul 0 0 x y) =
      A.mul 0 0 (A.iCycles 0 x) (A.iCycles 0 y) := by
    change ((forget₂ (ModuleCat R) Ab).map (A.iCycles 0))
      (A.toChainComplex.cyclesMk
        (A.nonnegativeMul (A.iCycles 0 x) (A.iCycles 0 y)) _ _ _) = _
    rw [HomologicalComplex.i_cyclesMk]
    rfl
  rw [h_mul]
  exact augmentation.map_mul _ _

/-- The canonical algebra homomorphism on zeroth homology induced by an augmentation.
Its function is the canonical homology map followed by the single-term homology comparison;
only the algebra laws are supplied separately. -/
noncomputable def homologyZeroMap (augmentation : Augmentation A S) :
    A.homologyZero →ₐ[R] S :=
  AlgHom.ofLinearMap augmentation.homologyZeroLinearMap
    augmentation.homologyZeroLinearMap_one augmentation.homologyZeroLinearMap_mul

/-- For a nonnegative source, the direct homology construction agrees with the map induced by
the associated chain-DGA homomorphism and the canonical degree-zero algebra comparison. -/
theorem homologyZeroMap_eq_comp_toChainHom (augmentation : Augmentation A S)
    [A.IsNonnegative] :
    augmentation.homologyZeroMap =
      (homologyZeroEquiv R S).toAlgHom.comp augmentation.toChainHom.homologyZeroMap := by
  apply AlgHom.ext
  intro x
  rfl

/-- Pulling back an augmentation composes its map on zeroth homology with the map induced by the
chain-DGA homomorphism. -/
@[simp]
theorem comp_homologyZeroMap [B.IsStrictlyCommutative]
    (augmentation : Augmentation B S) (f : Hom A B) :
    (augmentation.comp f).homologyZeroMap =
      augmentation.homologyZeroMap.comp f.homologyZeroMap := by
  apply AlgHom.ext
  intro x
  change (homologyZeroIso R S).hom
      (HomologicalComplex.homologyMap (f.toChainMap ≫ augmentation.toChainMap) 0 x) =
    (homologyZeroIso R S).hom
      (HomologicalComplex.homologyMap augmentation.toChainMap 0
        (HomologicalComplex.homologyMap f.toChainMap 0 x))
  rw [HomologicalComplex.homologyMap_comp]
  rfl

/-- On a cycle class, the canonical zeroth-homology map is the degree-zero component of the
augmentation. -/
@[simp] theorem homologyZeroMap_homologyπ (augmentation : Augmentation A S)
    (x : A.cycles 0) :
    augmentation.homologyZeroMap (A.homologyπ 0 x) =
      (degreeZeroIso R S).hom (augmentation.toChainMap.f 0 (A.iCycles 0 x)) := by
  exact augmentation.homologyZeroLinearMap_homologyπ x

/-- A quasi-isomorphic augmentation induces a bijection on canonical zeroth homology. -/
theorem homologyZeroMap_bijective (augmentation : Augmentation A S)
    [QuasiIso augmentation.toChainMap] :
    Function.Bijective augmentation.homologyZeroMap := by
  change Function.Bijective (fun x ↦ (homologyZeroIso R S).hom
    (HomologicalComplex.homologyMap augmentation.toChainMap 0 x))
  exact (ConcreteCategory.bijective_of_isIso (homologyZeroIso R S).hom).comp
    (ConcreteCategory.bijective_of_isIso
      (HomologicalComplex.homologyMap augmentation.toChainMap 0))

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
          sigma (augmentationA.homologyZeroMap x) := by
  constructor
  · intro h x
    exact congrArg (fun k : A.homologyZero →ₐ[R] T ↦ k x) h
  · intro h
    exact AlgHom.ext h

/-- The identity chain-DGA map commutes over the identity algebra map with any augmentation. -/
theorem commutesOnH0Over_id (augmentation : Augmentation A S) :
    (Hom.id A).CommutesOnH0Over (AlgHom.id R S) augmentation augmentation := by
  apply (commutesOnH0Over_iff _ _ _ _).mpr
  intro x
  change augmentation.homologyZeroMap
      (HomologicalComplex.homologyMap (𝟙 A.toChainComplex) 0 x) =
    augmentation.homologyZeroMap x
  rw [HomologicalComplex.homologyMap_id]
  rfl

/-- Commutation of augmentation squares is preserved by composition. -/
theorem commutesOnH0Over_comp
    {C : ChainDGAlgebra.{u, v} R} [C.IsStrictlyCommutative]
    {U : Type v} [CommRing U] [Algebra R U]
    {augmentationA : Augmentation A S} {augmentationB : Augmentation B T}
    {augmentationC : Augmentation C U}
    {f : Hom A B} {g : Hom B C} {sigma : S →ₐ[R] T} {tau : T →ₐ[R] U}
    (hf : f.CommutesOnH0Over sigma augmentationA augmentationB)
    (hg : g.CommutesOnH0Over tau augmentationB augmentationC) :
    (Hom.comp g f).CommutesOnH0Over (tau.comp sigma) augmentationA augmentationC := by
  apply (commutesOnH0Over_iff _ _ _ _).mpr
  intro x
  have hcomp : (Hom.comp g f).homologyZeroMap x =
      g.homologyZeroMap (f.homologyZeroMap x) := by
    change HomologicalComplex.homologyMap (f.toChainMap ≫ g.toChainMap) 0 x =
      HomologicalComplex.homologyMap g.toChainMap 0
        (HomologicalComplex.homologyMap f.toChainMap 0 x)
    rw [HomologicalComplex.homologyMap_comp]
    rfl
  change augmentationC.homologyZeroMap ((Hom.comp g f).homologyZeroMap x) =
    tau (sigma (augmentationA.homologyZeroMap x))
  rw [hcomp, (commutesOnH0Over_iff _ _ _ _).mp hg,
    (commutesOnH0Over_iff _ _ _ _).mp hf]

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
          augmentationA.homologyZeroMap x :=
  commutesOnH0Over_iff f (AlgHom.id R S) augmentationA augmentationB

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
    f = g := by
  cases f
  cases g
  cases h_chain
  cases h_target
  rfl

/-- The identity morphism of an augmented chain DGA. -/
def id (augmentation : Augmentation A S) : Augmentation.Hom augmentation augmentation where
  toChainHom := ChainDGAlgebra.Hom.id A
  toAlgHom := AlgHom.id R S
  commutesOnH0 := ChainDGAlgebra.Hom.commutesOnH0Over_id augmentation

/-- The chain-DGA map underlying the identity augmented morphism is the identity. -/
@[simp]
theorem id_toChainHom (augmentation : Augmentation A S) :
    (id augmentation).toChainHom = ChainDGAlgebra.Hom.id A := rfl

/-- The target-algebra map underlying the identity augmented morphism is the identity. -/
@[simp]
theorem id_toAlgHom (augmentation : Augmentation A S) :
    (id augmentation).toAlgHom = AlgHom.id R S := rfl

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
    (comp g f).toChainHom = ChainDGAlgebra.Hom.comp g.toChainHom f.toChainHom := rfl

/-- The target-algebra map underlying a composite augmented morphism is the composite map. -/
@[simp]
theorem comp_toAlgHom (g : Augmentation.Hom augmentationB augmentationC)
    (f : Augmentation.Hom augmentationA augmentationB) :
    (comp g f).toAlgHom = g.toAlgHom.comp f.toAlgHom := rfl

/-- Composing with the identity on the source leaves an augmented morphism unchanged. -/
@[simp]
theorem id_comp (f : Augmentation.Hom augmentationA augmentationB) :
    comp f (id augmentationA) = f := by
  apply ext
  · rfl
  · rfl

/-- Composing with the identity on the target leaves an augmented morphism unchanged. -/
@[simp]
theorem comp_id (f : Augmentation.Hom augmentationA augmentationB) :
    comp (id augmentationB) f = f := by
  apply ext
  · rfl
  · rfl

/-- Composition of augmented chain-DGA morphisms is associative. -/
theorem assoc
    {D : ChainDGAlgebra.{u, v} R} [D.IsStrictlyCommutative]
    {V : Type v} [CommRing V] [Algebra R V]
    {augmentationD : Augmentation D V}
    (h : Augmentation.Hom augmentationC augmentationD)
    (g : Augmentation.Hom augmentationB augmentationC)
    (f : Augmentation.Hom augmentationA augmentationB) :
    comp h (comp g f) = comp (comp h g) f := by
  apply ext
  · rfl
  · rfl

end Hom

end Augmentation

end ChainDGAlgebra
