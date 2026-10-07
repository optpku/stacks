module

public import stacks_project.Chap110.Lemma_110_43_1_Cotangent
public import ReasLib.RingTheory.DirectLimit.Algebra
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Directed limits of André-Quillen cotangent complexes

This leaf owns the canonical comparison from the degreewise module direct limit of
stagewise cotangent complexes, after scalar extension to the common target
direct-limit ring, to the cotangent complex of the induced map of ring direct
limits.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicTopology
open HomologicalComplex
open scoped Simplicial ZeroObject

universe u

noncomputable section

namespace Algebra.CotangentComplex

open CommRingCat.Under.CotangentComplex
open CommRingCat.Under.FreeAlgebra

/-- The polynomial-algebra ring map induced by a coefficient homomorphism and a
variable map. -/
def mvPolynomialRingHom {R S : Type u} [CommRing R] [CommRing S] {E F : Type u}
    (α : R →+* S) (φ : E → F) :
    MvPolynomial E R →+* MvPolynomial F S :=
  (MvPolynomial.rename (R := S) φ).toRingHom.comp (MvPolynomial.map α)

/-- Unfolding of `mvPolynomialRingHom` as coefficient change followed by renaming. -/
theorem mvPolynomialRingHom_eq {R S : Type u} [CommRing R] [CommRing S] {E F : Type u}
    (α : R →+* S) (φ : E → F) :
    mvPolynomialRingHom α φ =
      (MvPolynomial.rename (R := S) φ).toRingHom.comp (MvPolynomial.map α) :=
  sorry

/-- The map of categorical free algebras induced by a coefficient map and a
variable map. -/
def freeAlgebraRightHom {A A' : CommRingCat.{u}} {E F : Type u}
    (α : A ⟶ A') (φ : E → F) :
    (algebraic A E).right ⟶ (algebraic A' F).right :=
  (toPolynomial A E).right ≫
    CommRingCat.ofHom (mvPolynomialRingHom α.hom φ) ≫
    (fromPolynomial A' F).right

/-- The identity variable map over a coefficient identity induces the identity of
free algebras. -/
theorem freeAlgebraRightHom_id (A : CommRingCat.{u}) (E : Type u) :
    freeAlgebraRightHom (𝟙 A) (fun x : E ↦ x) = 𝟙 (algebraic A E).right :=
  sorry

/-- The ring map of iterated polynomial-algebra resolutions induced by a map of
under-objects changing both the base ring and the resolved algebra. -/
def iterateRightHom {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right) :
    (n : ℕ) →
      ((Endofunctor.iterate (CommRingCat.Under.PolynomialResolution.functor A) n).obj B).right ⟶
        ((Endofunctor.iterate (CommRingCat.Under.PolynomialResolution.functor A') n).obj B').right
  | 0 => β
  | n + 1 =>
      freeAlgebraRightHom α ((CategoryTheory.forget CommRingCat).map (iterateRightHom α β n))

/-- The zeroth iterate ring map is the given map of resolved algebras. -/
theorem iterateRightHom_zero {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right) :
    iterateRightHom α β 0 = β :=
  sorry

/-- The ring map of standard polynomial-resolution terms induced by a map of
under-objects changing both the base ring and the resolved algebra. -/
def standardTermRightHom {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right) (n : SimplexCategoryᵒᵖ) :
    (standardTerm A B n).right ⟶ (standardTerm A' B' n).right :=
  iterateRightHom α β (n.unop.len + 1)

/-- Structure maps of standard-resolution terms form a commutative square with the
induced termwise ring maps. -/
theorem standardTermRightHom_square {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    α ≫ (standardTerm A' B' n).hom =
      (standardTerm A B n).hom ≫ standardTermRightHom α β n :=
  sorry

/-- Augmentations of standard-resolution terms form a commutative square with the
induced termwise ring maps. -/
theorem standardTermRightHom_comp_augmentation {A A' : CommRingCat.{u}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    β.hom.comp (standardAugmentation A B n).hom =
      (standardAugmentation A' B' n).hom.comp (standardTermRightHom α β n).hom :=
  sorry

/-- The map of relative Kähler differentials of standard-resolution terms induced by a
commutative square of under-objects. -/
def standardDifferentialsMap {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    CommRingCat.KaehlerDifferential (standardTerm A B n).hom ⟶
      (ModuleCat.restrictScalars (standardTermRightHom α β n).hom).obj
        (CommRingCat.KaehlerDifferential (standardTerm A' B' n).hom) :=
  CommRingCat.KaehlerDifferential.map (standardTermRightHom_square α β hα n)

/-- Unfolding of `standardDifferentialsMap` as `CommRingCat.KaehlerDifferential.map`
of the standard-term structure-map square. -/
theorem standardDifferentialsMap_eq {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    standardDifferentialsMap α β hα n =
      CommRingCat.KaehlerDifferential.map (standardTermRightHom_square α β hα n) :=
  sorry

/-- The `B`-module comparison underlying a square map of simplicial cotangent terms,
before extension of scalars along the target ring map. -/
def standardBModuleMap {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    (simplicialModule A B).obj n ⟶
      (ModuleCat.restrictScalars β.hom).obj ((simplicialModule A' B').obj n) :=
  ((ModuleCat.extendRestrictScalarsAdj (standardAugmentation A B n).hom).homEquiv _ _).symm
    (standardDifferentialsMap α β hα n ≫
      (ModuleCat.restrictScalars (standardTermRightHom α β n).hom).map
        ((ModuleCat.extendRestrictScalarsAdj (standardAugmentation A' B' n).hom).unit.app _) ≫
      (ModuleCat.restrictScalarsComp' (standardTermRightHom α β n).hom
          (standardAugmentation A' B' n).hom
          (β.hom.comp (standardAugmentation A B n).hom)
          (standardTermRightHom_comp_augmentation α β hα n)).inv.app _)

/-- Degreewise map of polynomial-resolution simplicial modules after extending scalars
along the target ring map of a commutative square. -/
def simplicialMap {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    (ModuleCat.extendScalars β.hom).obj ((simplicialModule A B).obj n) ⟶
      (simplicialModule A' B').obj n :=
  ((ModuleCat.extendRestrictScalarsAdj β.hom).homEquiv _ _).symm
    (standardBModuleMap α β hα n)

/-- Unfolding of `simplicialMap` through the extension-restriction adjunction. -/
theorem simplicialMap_eq {A A' : CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    simplicialMap α β hα n =
      ((ModuleCat.extendRestrictScalarsAdj β.hom).homEquiv _ _).symm
        (standardBModuleMap α β hα n) :=
  sorry

/-- Degreewise map of polynomial-resolution simplicial modules induced by a
commutative square of ring homomorphisms. -/
def simplicialMap_ringHom {R S R' S' : Type u}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (f' : R' →+* S') (α : R →+* R') (β : S →+* S')
    (hcomm : f'.comp α = β.comp f) (n : SimplexCategoryᵒᵖ) :
    (ModuleCat.extendScalars β).obj
        ((simplicialModule (CommRingCat.of R) (Under.mk (CommRingCat.ofHom f))).obj n) ⟶
      (simplicialModule (CommRingCat.of R') (Under.mk (CommRingCat.ofHom f'))).obj n :=
  @simplicialMap (CommRingCat.of R) (CommRingCat.of R')
    (Under.mk (CommRingCat.ofHom f)) (Under.mk (CommRingCat.ofHom f'))
    (CommRingCat.ofHom α) (CommRingCat.ofHom β)
    (congrArg CommRingCat.ofHom hcomm) n

/-- The cochain map of André-Quillen cotangent complexes induced by a commutative
square of ring homomorphisms. -/
def map {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (f' : R' →+* S') (α : R →+* R') (β : S →+* S')
    (hcomm : f'.comp α = β.comp f) :
    ((ModuleCat.extendScalars β).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (RingHom.cotangentComplex f) ⟶
      RingHom.cotangentComplex f' where
  f i :=
    match h : ComplexShape.embeddingDownNat.r i with
    | some n =>
        (ModuleCat.extendScalars β).map
            (extendXIso
              ((alternatingFaceMapComplex (ModuleCat.{u} S)).obj
                (simplicialModule (CommRingCat.of R) (Under.mk (CommRingCat.ofHom f))))
              ComplexShape.embeddingDownNat
              (ComplexShape.embeddingDownNat.f_eq_of_r_eq_some h)).hom ≫
          simplicialMap_ringHom f f' α β hcomm (op ⦋n⦌) ≫
          (extendXIso
              ((alternatingFaceMapComplex (ModuleCat.{u} S')).obj
                (simplicialModule (CommRingCat.of R') (Under.mk (CommRingCat.ofHom f'))))
              ComplexShape.embeddingDownNat
              (ComplexShape.embeddingDownNat.f_eq_of_r_eq_some h)).inv
    | none => 0
  comm' := sorry

/-- Unfolding of `simplicialMap_ringHom` as `simplicialMap` of the corresponding
morphisms in `CommRingCat`. -/
theorem simplicialMap_ringHom_eq {R S R' S' : Type u}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (f' : R' →+* S') (α : R →+* R') (β : S →+* S')
    (hcomm : f'.comp α = β.comp f) (n : SimplexCategoryᵒᵖ) :
    simplicialMap_ringHom f f' α β hcomm n =
      @simplicialMap (CommRingCat.of R) (CommRingCat.of R')
        (Under.mk (CommRingCat.ofHom f)) (Under.mk (CommRingCat.ofHom f'))
        (CommRingCat.ofHom α) (CommRingCat.ofHom β)
        (congrArg CommRingCat.ofHom hcomm) n :=
  sorry

/-- A square map of cotangent complexes vanishes in strictly positive cohomological
degrees. -/
theorem map_zero_of_pos {R S R' S' : Type u}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (f' : R' →+* S') (α : R →+* R') (β : S →+* S')
    (hcomm : f'.comp α = β.comp f) {n : ℤ} (hn : 0 < n) :
    (map f f' α β hcomm).f n = 0 :=
  sorry

end Algebra.CotangentComplex

namespace Algebra.CotangentComplex.DirectLimit

variable {I : Type u} [Preorder I]
variable {R S : I → Type u}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
variable (ρ : ∀ i j, i ≤ j → R i →+* R j)
variable (σ : ∀ i j, i ≤ j → S i →+* S j)

/-- The ring homomorphism induced on direct limits by a compatible family of stage maps. -/
@[stacks 08S9]
noncomputable abbrev limitHom
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Ring.DirectLimit R (fun i j h ↦ ρ i j h) →+*
      Ring.DirectLimit S (fun i j h ↦ σ i j h) :=
  Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h

/-- Unfolding of `limitHom` as `Ring.DirectLimit.map` of the stage algebra maps. -/
@[stacks 08S9]
theorem limitHom_eq
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    limitHom ρ σ hcomm =
      Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h :=
  sorry

/-- The André-Quillen cotangent complex of the induced direct-limit algebra map. -/
@[stacks 08S9]
noncomputable def targetComplex
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    CochainComplex (ModuleCat.{u} (Ring.DirectLimit S (fun i j h ↦ σ i j h))) ℤ :=
  RingHom.cotangentComplex (limitHom ρ σ hcomm)

/-- Unfolding of `targetComplex` as the cotangent complex of `limitHom`. -/
@[stacks 08S9]
theorem targetComplex_eq
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    targetComplex ρ σ hcomm = RingHom.cotangentComplex (limitHom ρ σ hcomm) :=
  sorry

namespace Stage

/-- The André-Quillen cotangent complex at a stage, extended to the common target
direct-limit ring. -/
@[stacks 08S9]
noncomputable def complex (i : I) :
    CochainComplex (ModuleCat.{u} (Ring.DirectLimit S (fun i j h ↦ σ i j h))) ℤ :=
  ((ModuleCat.extendScalars (Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
    (Algebra.cotangentComplex (R i) (S i))

/-- The degree-`n` module in the common-target cotangent complex of a stage. -/
@[stacks 08S9]
noncomputable abbrev component (n : ℤ) (i : I) :
    ModuleCat.{u} (Ring.DirectLimit S (fun i j h ↦ σ i j h)) :=
  (complex (R := R) (S := S) (σ := σ) i).X n

/-- The two scalar-extension routes from a stage to the target direct limit give the
same source complex. -/
theorem complex_eq_extendScalars_comp {i j : I} (h : i ≤ j) :
    complex (R := R) (S := S) (σ := σ) i =
      ((ModuleCat.extendScalars
          ((Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j).comp (σ i j h))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (Algebra.cotangentComplex (R i) (S i)) :=
  sorry

/-- The canonical map from a stage cotangent complex after extending scalars to a
later stage, induced by the transition square. -/
@[stacks 08S9]
noncomputable def transition
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    complex (R := R) (S := S) (σ := σ) i ⟶ complex (R := R) (S := S) (σ := σ) j :=
  let C := Algebra.cotangentComplex (R i) (S i)
  let sigmaIJ : S i →+* S j := σ i j h
  let sigmaJTarget : S j →+* Ring.DirectLimit S (fun i j h ↦ σ i j h) :=
    Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j
  eqToHom
      (congrArg
        (fun φ : S i →+* Ring.DirectLimit S (fun i j h ↦ σ i j h) =>
          ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
        (RingHom.ext fun x =>
          (Ring.DirectLimit.of_f
            (f := fun i j hij => (σ i j hij : S i → S j)) h x).symm)) ≫
    (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp sigmaIJ sigmaJTarget)
        (ComplexShape.up ℤ)).hom.app C ≫
      ((ModuleCat.extendScalars sigmaJTarget).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Algebra.CotangentComplex.map (algebraMap (R i) (S i)) (algebraMap (R j) (S j))
          (ρ i j h) (σ i j h) (hcomm h))

/-- The canonical map from a stage complex to the cotangent complex of the
direct-limit algebra map. -/
@[stacks 08S9]
noncomputable def toTarget
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    complex (R := R) (S := S) (σ := σ) i ⟶ targetComplex ρ σ hcomm :=
  Algebra.CotangentComplex.map (algebraMap (R i) (S i)) (limitHom ρ σ hcomm)
    (Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) i)
    (Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i)
    (Ring.DirectLimit.Algebra.map_comp_of (ρ := ρ) (σ := σ)
      (fun k ↦ algebraMap (R k) (S k)) hcomm i)

/-- The degree-`n` linear transition map between common-target stage components. -/
@[stacks 08S9]
noncomputable abbrev componentMap
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n : ℤ) {i j : I} (h : i ≤ j) :
    component (R := R) (S := S) (σ := σ) n i →ₗ[Ring.DirectLimit S (fun i j h ↦ σ i j h)]
      component (R := R) (S := S) (σ := σ) n j :=
  ((transition ρ σ hcomm h).f n).hom

/-- The stage transition along an identity index relation is the identity chain map. -/
@[stacks 08S9]
theorem transition_id
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    transition ρ σ hcomm (le_rfl : i ≤ i) = 𝟙 _ :=
  sorry

/-- Stage transitions compose along composable index relations. -/
@[stacks 08S9]
theorem transition_comp
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    transition ρ σ hcomm hij ≫ transition ρ σ hcomm hjk =
      transition ρ σ hcomm (hij.trans hjk) :=
  sorry

/-- The maps from stages to the target direct-limit complex form a compatible
cocone over the stage transitions. -/
@[stacks 08S9]
theorem toTarget_comp_transition
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    transition ρ σ hcomm h ≫ toTarget ρ σ hcomm j = toTarget ρ σ hcomm i :=
  sorry

/-- The degree-`n` components of the canonical stage complexes form a directed
system whenever the base and target ring systems do. -/
@[stacks 08S9, instance]
theorem componentDirectedSystem
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n : ℤ) :
    DirectedSystem
      (fun i ↦ (component (R := R) (S := S) (σ := σ) n i : Type u))
      (fun {_ _} h x ↦ componentMap ρ σ hcomm n h x) :=
  sorry

/-- Stage differentials commute with the common-target stage transitions. -/
theorem differentialCompatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n m : ℤ) {i j : I} (h : i ≤ j) :
    ((complex (R := R) (S := S) (σ := σ) j).d n m).hom ∘ₗ
        ((transition ρ σ hcomm h).f n).hom =
      ((transition ρ σ hcomm h).f m).hom ∘ₗ
        ((complex (R := R) (S := S) (σ := σ) i).d n m).hom :=
  sorry

/-- The degree-`n` components of the stage-to-target maps are compatible with
stage transitions. -/
theorem toTarget_component_compatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n : ℤ) {i j : I} (h : i ≤ j)
    (x : component (R := R) (S := S) (σ := σ) n i) :
    ((toTarget ρ σ hcomm j).f n).hom (((transition ρ σ hcomm h).f n).hom x) =
      ((toTarget ρ σ hcomm i).f n).hom x :=
  sorry

end Stage

namespace Model

/-- The degree-`n` module of the direct-limit model. -/
@[stacks 08S9]
noncomputable abbrev component
    (n : ℤ)
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    ModuleCat.{u} (Ring.DirectLimit S (fun i j h ↦ σ i j h)) :=
  -- Local instance justification (defeq pin): `Module.DirectLimit` requires `DecidableEq I`; pin `Classical.decEq` so every degree uses the same instance.
  letI : DecidableEq I := Classical.decEq I
  ModuleCat.of (Ring.DirectLimit S (fun i j h ↦ σ i j h)) <|
    Module.DirectLimit
      (fun i ↦ (Stage.complex (R := R) (S := S) (σ := σ) i).X n)
      (fun _ _ h ↦ ((Stage.transition ρ σ hcomm h).f n).hom)

/-- The direct-limit cochain complex formed from the stagewise cotangent complexes
after extending scalars to the target direct limit. -/
@[stacks 08S9]
noncomputable def complex
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    CochainComplex (ModuleCat.{u} (Ring.DirectLimit S (fun i j h ↦ σ i j h))) ℤ where
  X n := component ρ σ n hcomm
  d n m :=
    -- Local instance justification (defeq pin): `Module.DirectLimit` requires `DecidableEq I`; pin `Classical.decEq` so every degree uses the same instance.
    letI : DecidableEq I := Classical.decEq I
    ModuleCat.ofHom <|
      Module.DirectLimit.map
        (fun i ↦ ((Stage.complex (R := R) (S := S) (σ := σ) i).d n m).hom)
        (fun _ _ h => Stage.differentialCompatible ρ σ hcomm n m h)
  shape := sorry
  d_comp_d' := sorry

/-- The degree-`n` object of the direct-limit model is the corresponding component. -/
theorem complex_X
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n : ℤ) :
    (complex ρ σ hcomm).X n = component ρ σ n hcomm :=
  sorry

end Model

/-- The canonical comparison from the direct-limit model of the stagewise cotangent
complexes to the cotangent complex of the direct-limit algebra map. -/
@[stacks 08S9]
noncomputable def comparison
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    Model.complex ρ σ hcomm ⟶ targetComplex ρ σ hcomm where
  f n :=
    -- Local instance justification (defeq pin): `Module.DirectLimit` requires `DecidableEq I`; pin `Classical.decEq` so every degree uses the same instance.
    letI : DecidableEq I := Classical.decEq I
    ModuleCat.ofHom <|
      Module.DirectLimit.lift
        (Ring.DirectLimit S (fun i j h ↦ σ i j h)) I
        (fun i ↦ (Stage.complex (R := R) (S := S) (σ := σ) i).X n)
        (fun _ _ h ↦ ((Stage.transition ρ σ hcomm h).f n).hom)
        (fun i ↦ ((Stage.toTarget ρ σ hcomm i).f n).hom)
        (fun _ _ h x => Stage.toTarget_component_compatible ρ σ hcomm n h x)
  comm' := sorry

/-- Chain-map commutativity for the canonical direct-limit comparison. -/
theorem comparison_comm
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (n m : ℤ) :
    (Model.complex ρ σ hcomm).d n m ≫ (comparison ρ σ hcomm).f m =
      (comparison ρ σ hcomm).f n ≫ (targetComplex ρ σ hcomm).d n m :=
  sorry

end Algebra.CotangentComplex.DirectLimit
