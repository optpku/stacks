module

public import stacks_project.Chap110.Lemma_110_43_1_Cotangent
public import stacks_project.Chap92.Lemma_92_3_4_DirectLimit
public import ReasLib.Algebra.Category.CommRingCat.Under.FreeAlgebra
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Transitivity triangle of André-Quillen cotangent complexes

For algebras `A → B → C`, this module owns the objects of `D(Mod C)` associated to
`Algebra.cotangentComplex A B`, `Algebra.cotangentComplex A C`, and
`Algebra.cotangentComplex B C`, together with the three maps of the transitivity
triangle `tensor A B C ⟶ derived A C ⟶ derived B C ⟶ (tensor A B C)⟦1⟧`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open HomologicalComplex
open Opposite
open AlgebraicTopology
open ComplexShape
open CochainComplex
open CochainComplex.HomComplex
open CommRingCat.Under.FreeAlgebra
open CommRingCat.Under.CotangentComplex
open scoped Simplicial
open scoped CategoryTheory.IteratedEndofunctor
open scoped TensorProduct
open scoped ChangeOfRings

noncomputable section

universe u

namespace Algebra.CotangentComplex

/-- The object of `Under (CommRingCat.of A)` associated to an `A`-algebra `B`. -/
abbrev under (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Under (CommRingCat.of A) :=
  Under.mk (CommRingCat.ofHom (algebraMap A B))

/-- Unfolding of `under` as the under-object of `algebraMap A B`. -/
theorem under_eq (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    under A B = Under.mk (CommRingCat.ofHom (algebraMap A B)) :=
  sorry

/-- The cotangent complex `L_{B/A}` as an object of `D(Mod B)`. -/
abbrev derived (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    DerivedCategory (ModuleCat.{u} B) :=
  DerivedCategory.Q.obj (Algebra.cotangentComplex A B)

/-- Unfolding of `derived` as `DerivedCategory.Q` of `Algebra.cotangentComplex`. -/
theorem derived_eq (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    derived A B = DerivedCategory.Q.obj (Algebra.cotangentComplex A B) :=
  sorry

/-- Cochain-level extension of scalars of `Algebra.cotangentComplex A B` along `B → C`. -/
abbrev tensorCochain (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    CochainComplex (ModuleCat.{u} C) ℤ :=
  ((ModuleCat.extendScalars (algebraMap B C)).mapHomologicalComplex (up ℤ)).obj
    (Algebra.cotangentComplex A B)

/-- `L_{B/A} ⊗^L_B C` in `D(Mod C)`, as the image of the cochain-level extension of the
standard cotangent complex. This is the source `⊗^L` on the free/K-projective terms of
`Algebra.cotangentComplex`, represented by `DerivedCategory.Q`. -/
abbrev tensor (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    DerivedCategory (ModuleCat.{u} C) :=
  DerivedCategory.Q.obj (tensorCochain A B C)

/-- Unfolding of `tensor` as `DerivedCategory.Q` of `tensorCochain`. -/
theorem tensor_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    tensor A B C = DerivedCategory.Q.obj (tensorCochain A B C) :=
  sorry

/-- Derived-functor form of `tensor`, as `derivedExtensionOfScalars` of `derived A B`. -/
abbrev tensorDerived (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    DerivedCategory (ModuleCat.{u} C) :=
  (ModuleCat.derivedExtensionOfScalars (algebraMap B C)).obj (derived A B)

/-- Unfolding of `tensorDerived` as `derivedExtensionOfScalars` of `derived A B`. -/
theorem tensorDerived_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    tensorDerived A B C =
      (ModuleCat.derivedExtensionOfScalars (algebraMap B C)).obj (derived A B) :=
  sorry

/-- The unextended first transitivity map
`Algebra.cotangentComplex A B ⊗_B C ⟶ Algebra.cotangentComplex A C`, as
`Algebra.CotangentComplex.map` of the square `id_A` and `B → C`. -/
def tensorMapCochain (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    tensorCochain A B C ⟶ Algebra.cotangentComplex A C :=
  map (algebraMap A B) (algebraMap A C) (RingHom.id A) (algebraMap B C)
    ((RingHom.comp_id (algebraMap A C)).trans (IsScalarTower.algebraMap_eq A B C))

/-- The first map `L_{B/A} ⊗^L_B C ⟶ L_{C/A}` of the transitivity triangle in `D(C)`. -/
def tensorMap (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    tensor A B C ⟶ derived A C :=
  DerivedCategory.Q.map (tensorMapCochain A B C)

/-- Unfolding of `tensorMap` as `DerivedCategory.Q.map` of `tensorMapCochain`. -/
theorem tensorMap_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    tensorMap A B C = DerivedCategory.Q.map (tensorMapCochain A B C) :=
  sorry

/-- The unextended second transitivity map
`Algebra.cotangentComplex A C ⟶ Algebra.cotangentComplex B C`, as the identity-scalar
adjustment of `map` of the square `A → B` and `id_C`. -/
def toRelativeMapCochain (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    Algebra.cotangentComplex A C ⟶ Algebra.cotangentComplex B C :=
  ((Functor.mapHomologicalComplexIdIso (ModuleCat.{u} C) (ComplexShape.up ℤ)).inv.app
      (Algebra.cotangentComplex A C)) ≫
    ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId C) (ComplexShape.up ℤ)).inv.app
      (Algebra.cotangentComplex A C)) ≫
      map (algebraMap A C) (algebraMap B C) (algebraMap A B) (RingHom.id C)
        ((IsScalarTower.algebraMap_eq A B C).symm.trans
          (RingHom.id_comp (algebraMap A C)).symm)

/-- Unfolding of `toRelativeMapCochain` as identity-scalar-extension followed by `map`. -/
theorem toRelativeMapCochain_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    toRelativeMapCochain A B C =
      ((Functor.mapHomologicalComplexIdIso (ModuleCat.{u} C) (ComplexShape.up ℤ)).inv.app
          (Algebra.cotangentComplex A C)) ≫
        ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId C)
            (ComplexShape.up ℤ)).inv.app (Algebra.cotangentComplex A C)) ≫
          map (algebraMap A C) (algebraMap B C) (algebraMap A B) (RingHom.id C)
            ((IsScalarTower.algebraMap_eq A B C).symm.trans
              (RingHom.id_comp (algebraMap A C)).symm) :=
  sorry

/-- The second map `L_{C/A} ⟶ L_{C/B}` of the transitivity triangle in `D(C)`. -/
def toRelativeMap (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    derived A C ⟶ derived B C :=
  DerivedCategory.Q.map (toRelativeMapCochain A B C)

/-- Unfolding of `toRelativeMap` as `DerivedCategory.Q.map` of `toRelativeMapCochain`. -/
theorem toRelativeMap_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    toRelativeMap A B C = DerivedCategory.Q.map (toRelativeMapCochain A B C) :=
  sorry

/-- The mapping cone of the unextended first transitivity map. -/
abbrev tensorMappingCone (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    CochainComplex (ModuleCat.{u} C) ℤ :=
  mappingCone (tensorMapCochain A B C)

/-- Unfolding of `tensorMappingCone` as `mappingCone` of `tensorMapCochain`. -/
theorem tensorMappingCone_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    tensorMappingCone A B C = mappingCone (tensorMapCochain A B C) :=
  sorry

/-- The simplicial `C`-module in degree `n` underlying `tensorCochain A B C`. -/
abbrev tensorSimplicial (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (n : SimplexCategoryᵒᵖ) : ModuleCat.{u} C :=
  (ModuleCat.extendScalars (algebraMap B C)).obj
    ((simplicialModule (CommRingCat.of A) (under A B)).obj n)

/-- The standard-resolution Kähler module `Ω_{P_n / A}` of `B` over `A`. -/
abbrev tensorKaehler (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (n : SimplexCategoryᵒᵖ) : ModuleCat.{u} (standardTerm (CommRingCat.of A) (under A B) n).right :=
  CommRingCat.KaehlerDifferential (standardTerm (CommRingCat.of A) (under A B) n).hom

/-- Underlying type of the degree-`n` standard `B`-resolution of `C`, which indexes the free
generators of the degree-`(n+1)` standard `B`-algebra. -/
abbrev connectingGenerators (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) : Type u :=
  (standardTerm (CommRingCat.of B) (under B C) (op ⦋n⦌)).right

/-- Unfolding of `connectingGenerators` as the carrier of the degree-`n` standard term. -/
theorem connectingGenerators_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    connectingGenerators A B C n =
      (standardTerm (CommRingCat.of B) (under B C) (op ⦋n⦌)).right :=
  sorry

/-- Free-forgetful unit including the previous iterate into the degree-`(n+1)` standard
`B`-algebra `R_{n+1}`. -/
def connectingGeneratorInclude (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    connectingGenerators A B C n →
      (standardTerm (CommRingCat.of B) (under B C) (op ⦋n + 1⦌)).right :=
  generator (A := CommRingCat.of B) (E := connectingGenerators A B C n)

/-- Unfolding of `connectingGeneratorInclude` as the universal generator of the free
`B`-algebra on the previous iterate. -/
theorem connectingGeneratorInclude_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    connectingGeneratorInclude A B C n =
      generator (A := CommRingCat.of B) (E := connectingGenerators A B C n) :=
  sorry

/-- Polynomial evaluation of the free `B`-algebra on the previous iterate at the
free-forgetful unit of `R_{n+1}`. -/
def connectingPolyEval (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    MvPolynomial (connectingGenerators A B C n) B →+*
      (standardTerm (CommRingCat.of B) (under B C) (op ⦋n + 1⦌)).right :=
  (fromPolynomial (CommRingCat.of B) (connectingGenerators A B C n)).right.hom

/-- Polynomial evaluation sends the variable of a previous-iterate element to the
corresponding free generator of `R_{n+1}`. -/
theorem connectingPolyEval_X (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ)
    (y : connectingGenerators A B C n) :
    connectingPolyEval A B C n (MvPolynomial.X y) =
      connectingGeneratorInclude A B C n y :=
  sorry

/-- The `B`-coefficient of a degree-`n` standard `B`-resolution element, via the polynomial
model of the free `B`-algebra. -/
def connectingToBase (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ)
    (y : connectingGenerators A B C n) : B :=
  MvPolynomial.constantCoeff
    ((toPolynomial (CommRingCat.of B)
        ((Endofunctor.iterate (comonadFunctor (CommRingCat.of B)) n).obj
          (under B C)).right).right
      y)

/-- Unfolding of `connectingToBase` as the constant coefficient of the polynomial model. -/
theorem connectingToBase_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ)
    (y : connectingGenerators A B C n) :
    connectingToBase A B C n y =
      MvPolynomial.constantCoeff
        ((toPolynomial (CommRingCat.of B)
            ((Endofunctor.iterate (comonadFunctor (CommRingCat.of B)) n).obj
              (under B C)).right).right
          y) :=
  sorry

/-- Iterated free generator in `P_n` of the `B`-coefficient of a free generator index `y`
of the degree-`(n+1)` standard `B`-algebra. -/
def connectingGenerator (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ)
    (y : connectingGenerators A B C n) :
    (standardTerm (CommRingCat.of A) (under A B) (op ⦋n⦌)).right :=
  generator.iterate (A := CommRingCat.of A) (under A B) n (connectingToBase A B C n y)

/-- Unfolding of `connectingGenerator` as `generator.iterate` of `connectingToBase`. -/
theorem connectingGenerator_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ)
    (y : connectingGenerators A B C n) :
    connectingGenerator A B C n y =
      generator.iterate (A := CommRingCat.of A) (under A B) n
        (connectingToBase A B C n y) :=
  sorry

/-- Image of `d(y)` in the unextended simplicial term `Ω_{P_n / A} ⊗ B`. -/
def connectingGeneratorExtend (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ)
    (y : connectingGenerators A B C n) :
    (simplicialModule (CommRingCat.of A) (under A B)).obj (op ⦋n⦌) :=
  ((ModuleCat.extendRestrictScalarsAdj
      (standardAugmentation (CommRingCat.of A) (under A B) (op ⦋n⦌)).hom).unit.app
    (tensorKaehler A B (op ⦋n⦌)))
    (CommRingCat.KaehlerDifferential.d (connectingGenerator A B C n y))

/-- Unfolding of `connectingGeneratorExtend` as the adjunction unit applied to
`d(connectingGenerator y)`. -/
theorem connectingGeneratorExtend_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ)
    (y : connectingGenerators A B C n) :
    connectingGeneratorExtend A B C n y =
      ((ModuleCat.extendRestrictScalarsAdj
          (standardAugmentation (CommRingCat.of A) (under A B) (op ⦋n⦌)).hom).unit.app
        (tensorKaehler A B (op ⦋n⦌)))
        (CommRingCat.KaehlerDifferential.d (connectingGenerator A B C n y)) :=
  sorry

/-- Image of `d(y)` in the degree-`n` term of `tensorCochain A B C`. -/
def connectingGeneratorValue (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ)
    (y : connectingGenerators A B C n) :
    tensorSimplicial A B C (op ⦋n⦌) :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap B C)).unit.app
      ((simplicialModule (CommRingCat.of A) (under A B)).obj (op ⦋n⦌)))
    (connectingGeneratorExtend A B C n y)

/-- Unfolding of `connectingGeneratorValue` as extension of scalars of
`connectingGeneratorExtend`. -/
theorem connectingGeneratorValue_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ)
    (y : connectingGenerators A B C n) :
    connectingGeneratorValue A B C n y =
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap B C)).unit.app
          ((simplicialModule (CommRingCat.of A) (under A B)).obj (op ⦋n⦌)))
        (connectingGeneratorExtend A B C n y) :=
  sorry

/-- Polynomial-model augmentation `B[E] → C` of the degree-`(n+1)` free `B`-algebra. -/
def connectingPolyAug (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    MvPolynomial (connectingGenerators A B C n) B →+* C :=
  (standardAugmentation (CommRingCat.of B) (under B C) (op ⦋n + 1⦌)).hom.comp
    (fromPolynomial (CommRingCat.of B) (connectingGenerators A B C n)).right.hom

/-- Polynomial-model assignment of `p ∈ B[E]` to
`∑ y, connectingPolyAug (MvPolynomial.pderiv y p) • connectingGeneratorValue y`
in the restricted tensor term. -/
def connectingPolyAssign (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ)
    (p : MvPolynomial (connectingGenerators A B C n) B) :
    (ModuleCat.restrictScalars (connectingPolyAug A B C n)).obj
      (tensorSimplicial A B C (op ⦋n⦌)) :=
  Finset.sum (MvPolynomial.vars p) fun y =>
    connectingPolyAug A B C n (MvPolynomial.pderiv y p) •
      connectingGeneratorValue A B C n y

/-- The assignment sends the variable `X y` to `connectingGeneratorValue y`. -/
theorem connectingPolyAssign_X (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ)
    (y : connectingGenerators A B C n) :
    connectingPolyAssign A B C n (MvPolynomial.X y) =
      connectingGeneratorValue A B C n y :=
  sorry

/-- Polynomial-model derivation of `B[E]` over `B` with values in the restricted
degree-`n` tensor term, sending each variable to `connectingGeneratorValue`. -/
def connectingPolyDerivation (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    ((ModuleCat.restrictScalars (connectingPolyAug A B C n)).obj
        (tensorSimplicial A B C (op ⦋n⦌))).Derivation
      (polynomial (CommRingCat.of B) (connectingGenerators A B C n)).hom :=
  ModuleCat.Derivation.mk (connectingPolyAssign A B C n)
    (fun _ _ => sorry) (fun _ _ => sorry) (fun _ => sorry)

/-- Polynomial-model Kähler map sending `d(X_y)` to `connectingGeneratorValue y`, as the
free-module universal property of `Ω_{B[E] / B}`. -/
def connectingPolyKaehler (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    CommRingCat.KaehlerDifferential
        (polynomial (CommRingCat.of B) (connectingGenerators A B C n)).hom ⟶
      (ModuleCat.restrictScalars (connectingPolyAug A B C n)).obj
        (tensorSimplicial A B C (op ⦋n⦌)) :=
  (connectingPolyDerivation A B C n).desc

/-- Unfolding of `connectingPolyKaehler` as `ModuleCat.Derivation.desc` of
`connectingPolyDerivation`. -/
theorem connectingPolyKaehler_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    connectingPolyKaehler A B C n = (connectingPolyDerivation A B C n).desc :=
  sorry


/-- The comparison square identifying the degree-`(n+1)` standard `B`-algebra with its
polynomial model, used to transport Kähler differentials. -/
theorem connectingToPolynomial_w (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    𝟙 (CommRingCat.of B) ≫
        (polynomial (CommRingCat.of B) (connectingGenerators A B C n)).hom =
      (standardTerm (CommRingCat.of B) (under B C) (op ⦋n + 1⦌)).hom ≫
        (toPolynomial (CommRingCat.of B) (connectingGenerators A B C n)).right :=
  sorry

/-- Compatibility of the polynomial-model augmentation with `toPolynomial`. -/
theorem connectingPolyAug_comp_toPolynomial (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    (standardAugmentation (CommRingCat.of B) (under B C) (op ⦋n + 1⦌)).hom =
      (connectingPolyAug A B C n).comp
        (toPolynomial (CommRingCat.of B) (connectingGenerators A B C n)).right.hom :=
  sorry

/-- Carrier-identity comparison from the polynomial-restricted tensor term to the
augmentation-restricted tensor term. -/
def connectingRestrict (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    (ModuleCat.restrictScalars
        (toPolynomial (CommRingCat.of B) (connectingGenerators A B C n)).right.hom).obj
      ((ModuleCat.restrictScalars (connectingPolyAug A B C n)).obj
        (tensorSimplicial A B C (op ⦋n⦌))) ⟶
    (ModuleCat.restrictScalars
        (standardAugmentation (CommRingCat.of B) (under B C) (op ⦋n + 1⦌)).hom).obj
      (tensorSimplicial A B C (op ⦋n⦌)) :=
  (ModuleCat.restrictScalarsComp'
      (toPolynomial (CommRingCat.of B) (connectingGenerators A B C n)).right.hom
      (connectingPolyAug A B C n)
      (standardAugmentation (CommRingCat.of B) (under B C) (op ⦋n + 1⦌)).hom
      (connectingPolyAug_comp_toPolynomial A B C n)).inv.app
    (tensorSimplicial A B C (op ⦋n⦌))

/-- Kähler-level transitivity boundary
`Ω_{R_{n+1} / B} ⟶ (Ω_{P_n / A} ⊗ B) ⊗_B C`. -/
def connectingKaehler (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    CommRingCat.KaehlerDifferential
        (standardTerm (CommRingCat.of B) (under B C) (op ⦋n + 1⦌)).hom ⟶
      (ModuleCat.restrictScalars
          (standardAugmentation (CommRingCat.of B) (under B C) (op ⦋n + 1⦌)).hom).obj
        (tensorSimplicial A B C (op ⦋n⦌)) :=
  CommRingCat.KaehlerDifferential.map (connectingToPolynomial_w A B C n) ≫
    (ModuleCat.restrictScalars
        (toPolynomial (CommRingCat.of B) (connectingGenerators A B C n)).right.hom).map
      (connectingPolyKaehler A B C n) ≫
    connectingRestrict A B C n

/-- Simplicial transitivity boundary
`Ω_{R_{n+1} / B} ⊗ C ⟶ (Ω_{P_n / A} ⊗ B) ⊗_B C`. -/
def connectingSimplicialBoundary (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    (simplicialModule (CommRingCat.of B) (under B C)).obj (op ⦋n + 1⦌) ⟶
      tensorSimplicial A B C (op ⦋n⦌) :=
  ((ModuleCat.extendRestrictScalarsAdj
      (standardAugmentation (CommRingCat.of B) (under B C) (op ⦋n + 1⦌)).hom).homEquiv _ _).symm
    (connectingKaehler A B C n)

/-- Degreewise transitivity boundary, nonzero only when the simplicial degrees differ by `1`. -/
def connectingSimplicialMap (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n m : ℕ) :
    (simplicialModule (CommRingCat.of B) (under B C)).obj (op ⦋n⦌) ⟶
      tensorSimplicial A B C (op ⦋m⦌) :=
  if h : n = m + 1 then
    eqToHom
        (congrArg
          (fun k : ℕ =>
            (simplicialModule (CommRingCat.of B) (under B C)).obj (op ⦋k⦌))
          h) ≫
      connectingSimplicialBoundary A B C m
  else
    0

/-- The cochain-level components of the mapping-cone comparison, in every cohomological
degree. -/
def connectingPredMap (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (i : ℤ) :
    (Algebra.cotangentComplex B C).X i ⟶ (tensorCochain A B C).X (i + 1) :=
  match hs : embeddingDownNat.r i, ht : embeddingDownNat.r (i + 1) with
  | some n, some m =>
      (extendXIso
          ((alternatingFaceMapComplex (ModuleCat.{u} C)).obj
            (simplicialModule (CommRingCat.of B) (under B C)))
          embeddingDownNat
          (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) hs)).hom ≫
        connectingSimplicialMap A B C n m ≫
        (ModuleCat.extendScalars (algebraMap B C)).map
          (extendXIso
              ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
                (simplicialModule (CommRingCat.of A) (under A B)))
              embeddingDownNat
              (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) ht)).inv
  | _, _ => 0

/-- Comparison of `L_{C/B}` into the mapping cone of the first transitivity map. -/
def toMappingConeCochain (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    Algebra.cotangentComplex B C ⟶ mappingCone (tensorMapCochain A B C) where
  f i :=
    connectingPredMap A B C i ≫
      (mappingCone.inl (tensorMapCochain A B C)).v (i + 1) i
        (add_neg_cancel_right i 1)
  comm' := sorry

/-- Unfolding of `toMappingConeCochain` along `mappingCone.inl`. -/
theorem toMappingConeCochain_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (i : ℤ) :
    (toMappingConeCochain A B C).f i =
      connectingPredMap A B C i ≫
        (mappingCone.inl (tensorMapCochain A B C)).v (i + 1) i
          (add_neg_cancel_right i 1) :=
  sorry

/-- Connecting cochain of the transitivity triangle, before passage to `D(C)`. -/
def connectingCochain (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    Algebra.cotangentComplex B C ⟶ (tensorCochain A B C)⟦(1 : ℤ)⟧ :=
  toMappingConeCochain A B C ≫
    (mappingCone.triangle (tensorMapCochain A B C)).mor₃


/-- The connecting map `L_{C/B} ⟶ (L_{B/A} ⊗^L_B C)⟦1⟧` of the transitivity triangle. -/
def connectingMap (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    derived B C ⟶ (tensor A B C)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map (connectingCochain A B C) ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (tensorCochain A B C)

/-- Unfolding of `connectingMap` as `Q.map` of the 08SD connecting cochain. -/
theorem connectingMap_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    connectingMap A B C =
      DerivedCategory.Q.map (connectingCochain A B C) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (tensorCochain A B C) :=
  sorry

/-- The displayed transitivity triangle of cotangent complexes in `D(C)`. -/
def transitivityTriangle (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    Triangle (DerivedCategory (ModuleCat.{u} C)) :=
  Triangle.mk (tensorMap A B C) (toRelativeMap A B C) (connectingMap A B C)

/-- The first vertex of `transitivityTriangle` is `tensor A B C`. -/
theorem transitivityTriangle_obj₁ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (transitivityTriangle A B C).obj₁ = tensor A B C :=
  sorry

/-- The second vertex of `transitivityTriangle` is `derived A C`. -/
theorem transitivityTriangle_obj₂ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (transitivityTriangle A B C).obj₂ = derived A C :=
  sorry

/-- The third vertex of `transitivityTriangle` is `derived B C`. -/
theorem transitivityTriangle_obj₃ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (transitivityTriangle A B C).obj₃ = derived B C :=
  sorry

/-- The first morphism of `transitivityTriangle` is `tensorMap`. -/
theorem transitivityTriangle_mor₁ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (transitivityTriangle A B C).mor₁ = tensorMap A B C :=
  sorry

/-- The second morphism of `transitivityTriangle` is `toRelativeMap`. -/
theorem transitivityTriangle_mor₂ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (transitivityTriangle A B C).mor₂ = toRelativeMap A B C :=
  sorry

/-- The third morphism of `transitivityTriangle` is `connectingMap`. -/
theorem transitivityTriangle_mor₃ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (transitivityTriangle A B C).mor₃ = connectingMap A B C :=
  sorry

/-- The transitivity triangle of cotangent complexes is distinguished in `D(C)`. -/
theorem transitivityTriangle_distinguished (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    transitivityTriangle A B C ∈ distTriang (DerivedCategory (ModuleCat.{u} C)) :=
  sorry

end Algebra.CotangentComplex
