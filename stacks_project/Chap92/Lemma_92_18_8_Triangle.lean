module

public import stacks_project.Chap92.Definition_92_22_1_Cotangent
public import stacks_project.Chap92.Lemma_92_18_7_Functoriality
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Natural
public import ReasLib.CategoryTheory.Adjunction.Iteration
public import ReasLib.CategoryTheory.Sites.AlgebraicSheaf.FreeAlgebra
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Transitivity triangle of sheaf cotangent complexes

For homomorphisms `A ⟶ B ⟶ C` of sheaves of rings on a site, this module owns the
canonical triangle `L(φ) ⊗^L C ⟶ L(φ ≫ ψ) ⟶ L(ψ) ⟶ (L(φ) ⊗^L C)⟦1⟧` in `D(C)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open HomologicalComplex
open ComplexShape
open Opposite
open AlgebraicTopology
open CochainComplex
open CochainComplex.HomComplex
open SheafOfModules.RingedSite
open scoped Simplicial
open scoped SheafOfModules.RingedSite.CotangentComplex
open scoped CategoryTheory.IteratedEndofunctor

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex

variable {D : Type u} [Category.{u} D] {J : GrothendieckTopology D}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [UnivLE.{u, u}]

-- Local instance justification (defeq pin): `moduleCategoryHasDerivedCategory` is the reducible standard owner for ringed-site modules; `DerivedCategory.Q` and `distTriang` need that same instance without registering a second derived-category owner.
attribute [local instance] moduleCategoryHasDerivedCategory

/-- Cochain-level extension of scalars of `L(φ)` along `ψ : B ⟶ C`. -/
abbrev tensorCochain {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    CochainComplex (SheafOfModules (ringSheaf J C)) ℤ :=
  ((extendAlong ψ).mapHomologicalComplex (up ℤ)).obj L(φ)

/-- `L(φ) ⊗^L_B C` in `D(C)`, as the image of the cochain-level extension of the standard
sheaf cotangent complex. -/
abbrev tensor {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    DerivedCategory (SheafOfModules (ringSheaf J C)) :=
  DerivedCategory.Q.obj (tensorCochain φ ψ)

/-- Unfolding of `tensor` as `DerivedCategory.Q` of `tensorCochain`. -/
theorem tensor_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    tensor φ ψ = DerivedCategory.Q.obj (tensorCochain φ ψ) :=
  sorry

/-- Derived-functor form of `tensor`, as `SameSite.pullbackDerived` of `L(φ)`. -/
abbrev tensorDerived {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    DerivedCategory (SheafOfModules (ringSheaf J C)) :=
  (SameSite.pullbackDerived ψ).obj (DerivedCategory.Q.obj L(φ))

/-- Unfolding of `tensorDerived` as `SameSite.pullbackDerived` of `Q.obj L(φ)`. -/
theorem tensorDerived_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    tensorDerived φ ψ =
      (SameSite.pullbackDerived ψ).obj (DerivedCategory.Q.obj L(φ)) :=
  sorry

/-- The morphism of `Under A` corresponding to `ψ : B ⟶ C` over the composite `φ ≫ ψ`. -/
def tensorUnderHom {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    Under.mk φ ⟶ Under.mk (φ ≫ ψ) :=
  Under.homMk ψ

/-- The unextended first transitivity map `L(φ) ⊗_B C ⟶ L(φ ≫ ψ)`, as `map` of `tensorUnderHom`. -/
def tensorMapCochain {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    tensorCochain φ ψ ⟶ L(φ ≫ ψ) :=
  map (tensorUnderHom φ ψ)

/-- The first map `L(φ) ⊗^L_B C ⟶ L(φ ≫ ψ)` of the transitivity triangle in `D(C)`. -/
def tensorMap {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    tensor φ ψ ⟶ DerivedCategory.Q.obj L(φ ≫ ψ) :=
  DerivedCategory.Q.map (tensorMapCochain φ ψ)

/-- Unfolding of `tensorMap` as `DerivedCategory.Q.map` of `tensorMapCochain`. -/
theorem tensorMap_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    tensorMap φ ψ = DerivedCategory.Q.map (tensorMapCochain φ ψ) :=
  sorry

/-- The free-forgetful comonad endofunctor on algebras under a fixed ring sheaf. -/
def freeForgetEndo (A : Sheaf J CommRingCat.{u}) : Under A ⥤ Under A :=
  (freeForgetAdjunction A).toComonad.toFunctor

/-- The iterated ring-sheaf map of standard-resolution terms induced by a map of bases and
resolved algebras. -/
def iterateRightHom {A A' : Sheaf J CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right) :
    (n : ℕ) →
      ((Endofunctor.iterate (freeForgetEndo A) n).obj B).right ⟶
        ((Endofunctor.iterate (freeForgetEndo A') n).obj B').right
  | 0 => β
  | n + 1 =>
      coprod.map α
        ((Sheaf.composeAndSheafify J CommRingCat.free).map
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map
            (iterateRightHom α β n)))

/-- The ring-sheaf map of standard-resolution terms induced by a map of bases and resolved
algebras. -/
irreducible_def standardTermRightHom {A A' : Sheaf J CommRingCat.{u}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (n : SimplexCategoryᵒᵖ) :
    (standardTerm A B n).right ⟶ (standardTerm A' B' n).right :=
  iterateRightHom α β (n.unop.len + 1)

/-- Structure maps of standard-resolution terms form a commutative square with the induced
termwise ring-sheaf maps. -/
theorem standardTermRightHom_square {A A' : Sheaf J CommRingCat.{u}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    α ≫ (standardTerm A' B' n).hom =
      (standardTerm A B n).hom ≫ standardTermRightHom α β n :=
  sorry

/-- Augmentations of standard-resolution terms form a commutative square with the induced
termwise ring-sheaf maps. -/
theorem standardTermRightHom_comp_augmentation {A A' : Sheaf J CommRingCat.{u}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    ringSheafMap (standardAugmentation A B n ≫ β) =
      ringSheafMap (standardTermRightHom α β n) ≫
        ringSheafMap (standardAugmentation A' B' n) :=
  sorry

/-- The identity on `C` is compatible with change of base along `φ` for the composite `φ ≫ ψ`. -/
theorem toRelative_w {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    φ ≫ ψ = (φ ≫ ψ) ≫ 𝟙 C :=
  sorry

/-- The commutative square of structure maps used by the second transitivity map. -/
theorem relativeTermSquare {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    CommSq φ (standardTerm A (Under.mk (φ ≫ ψ)) n).hom
      (standardTerm B (Under.mk ψ) n).hom (standardTermRightHom φ (𝟙 C) n) :=
  sorry

/-- Termwise base-change of relative differentials along `relativeTermSquare`. -/
def relativeDifferentialsTermMap {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    relativeDifferentials (standardTerm A (Under.mk (φ ≫ ψ)) n).hom ⟶
      (restrictionAlong (standardTermRightHom φ (𝟙 C) n)).obj
        (relativeDifferentials (standardTerm B (Under.mk ψ) n).hom) :=
  RelativeDifferentials.map (relativeTermSquare φ ψ n)

/-- Ring-level augmentation compatibility for `relativeTermSquare`. -/
theorem relativeAugmentation_comp_ring {A B C : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) (ψ : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    ringSheafMap (standardAugmentation A (Under.mk (φ ≫ ψ)) n) =
      ringSheafMap (standardTermRightHom φ (𝟙 C) n) ≫
        ringSheafMap (standardAugmentation B (Under.mk ψ) n) :=
  sorry

/-- Restriction along `standardTermRightHom` of `Ω_{R_n/B}` agrees with restriction along the
`C/A` augmentation of the `C/B` simplicial cotangent term. -/
theorem relativeRestrictedTarget_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    (restrictionAlong (standardTermRightHom φ (𝟙 C) n)).obj
      (relativeDifferentials (standardTerm B (Under.mk ψ) n).hom) =
    (restrictionAlong (standardAugmentation A (Under.mk (φ ≫ ψ)) n)).obj
      ((simplicialModule B (Under.mk ψ)).obj n) :=
  sorry

/-- The restricted target of `relativeDifferentialsTermMap` after transporting along the
augmentation of the `C/A` standard-resolution term. -/
def relativeRestrictedMap {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    relativeDifferentials (standardTerm A (Under.mk (φ ≫ ψ)) n).hom ⟶
      (restrictionAlong (standardAugmentation A (Under.mk (φ ≫ ψ)) n)).obj
        ((simplicialModule B (Under.mk ψ)).obj n) :=
  relativeDifferentialsTermMap φ ψ n ≫ eqToHom (relativeRestrictedTarget_eq φ ψ n)

/-- Degreewise second transitivity map of simplicial cotangent modules, changing the base
ring sheaf while keeping the total algebra `C`. -/
def relativeSimplicialMap {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    (simplicialModule A (Under.mk (φ ≫ ψ))).obj n ⟶
      (simplicialModule B (Under.mk ψ)).obj n :=
  ((extendRestrictAdj (standardAugmentation A (Under.mk (φ ≫ ψ)) n)).homEquiv _ _).symm
    (relativeRestrictedMap φ ψ n)

/-- The unextended second transitivity map `L(φ ≫ ψ) ⟶ L(ψ)`, induced by base change of
relative differentials along `φ`. -/
def toRelativeMapCochain {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    L(φ ≫ ψ) ⟶ L(ψ) where
  f i :=
    match h : embeddingDownNat.r i with
    | some n =>
        (extendXIso
            ((alternatingFaceMapComplex (SheafOfModules (ringSheaf J C))).obj
              (simplicialModule A (Under.mk (φ ≫ ψ))))
            embeddingDownNat
            (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).hom ≫
          relativeSimplicialMap φ ψ (op ⦋n⦌) ≫
          (extendXIso
              ((alternatingFaceMapComplex (SheafOfModules (ringSheaf J C))).obj
                (simplicialModule B (Under.mk ψ)))
              embeddingDownNat
              (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).inv
    | none => 0
  comm' := sorry

/-- The second map `L(φ ≫ ψ) ⟶ L(ψ)` of the transitivity triangle in `D(C)`. -/
def toRelativeMap {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    DerivedCategory.Q.obj L(φ ≫ ψ) ⟶ DerivedCategory.Q.obj L(ψ) :=
  DerivedCategory.Q.map (toRelativeMapCochain φ ψ)

/-- Unfolding of `toRelativeMap` as `DerivedCategory.Q.map` of `toRelativeMapCochain`. -/
theorem toRelativeMap_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    toRelativeMap φ ψ = DerivedCategory.Q.map (toRelativeMapCochain φ ψ) :=
  sorry

/-- The simplicial `C`-module in degree `n` underlying `tensorCochain φ ψ`. -/
abbrev tensorSimplicial {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) : SheafOfModules (ringSheaf J C) :=
  (extendAlong ψ).obj ((simplicialModule A (Under.mk φ)).obj n)

/-- Restriction of the degree-`n` tensor term along the augmentation of the degree-`(n+1)`
`C/B` standard-resolution algebra. -/
abbrev connectingTarget {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    SheafOfModules (ringSheaf J (standardTerm B (Under.mk ψ) (op ⦋n + 1⦌)).right) :=
  (restrictionAlong (standardAugmentation B (Under.mk ψ) (op ⦋n + 1⦌))).obj
    (tensorSimplicial φ ψ (op ⦋n⦌))

/-- Unfolding of `connectingTarget` as restriction of the extended degree-`n` `B/A` term. -/
theorem connectingTarget_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : ℕ) :
    connectingTarget φ ψ n =
      (restrictionAlong (standardAugmentation B (Under.mk ψ) (op ⦋n + 1⦌))).obj
        (tensorSimplicial φ ψ (op ⦋n⦌)) :=
  sorry

/-- Underlying sheaf of sets of the degree-`n` `C/B` standard-resolution algebra. -/
abbrev connectingGenerators {B C : Sheaf J CommRingCat.{u}} (ψ : B ⟶ C) (n : ℕ) :
    Sheaf J (Type u) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
    (standardTerm B (Under.mk ψ) (op ⦋n⦌)).right

/-- Unfolding of `connectingGenerators` as the underlying sheaf of the degree-`n` term. -/
theorem connectingGenerators_eq {B C : Sheaf J CommRingCat.{u}} (ψ : B ⟶ C) (n : ℕ) :
    connectingGenerators ψ n =
      (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
        (standardTerm B (Under.mk ψ) (op ⦋n⦌)).right :=
  sorry

/-- The free-forgetful unit including the previous iterate into the free `B`-algebra on that
iterate. -/
def connectingGeneratorInclude {B C : Sheaf J CommRingCat.{u}} (ψ : B ⟶ C) (n : ℕ) :
    connectingGenerators ψ n ⟶
      (sheafForget J).obj (CategoryTheory.Sheaf.FreeAlgebra.underlying B (connectingGenerators ψ n)) :=
  CategoryTheory.Sheaf.FreeAlgebra.generator B (connectingGenerators ψ n)

/-- Unfolding of `connectingGeneratorInclude` as `CategoryTheory.Sheaf.FreeAlgebra.generator`. -/
theorem connectingGeneratorInclude_eq {B C : Sheaf J CommRingCat.{u}} (ψ : B ⟶ C)
    (n : ℕ) :
    connectingGeneratorInclude ψ n = CategoryTheory.Sheaf.FreeAlgebra.generator B (connectingGenerators ψ n) :=
  sorry

/-- Evaluation of the free `B`-algebra on the previous `C/B` iterate at the free-forgetful unit
of `R_{n+1}`. -/
def connectingFreeEval {B C : Sheaf J CommRingCat.{u}} (ψ : B ⟶ C) (n : ℕ) :
    CategoryTheory.Sheaf.FreeAlgebra.obj B (connectingGenerators ψ n) ⟶
      Under.mk (standardTerm B (Under.mk ψ) (op ⦋n + 1⦌)).hom :=
  CategoryTheory.Sheaf.FreeAlgebra.evaluation
    (Under.mk (standardTerm B (Under.mk ψ) (op ⦋n + 1⦌)).hom)
    (connectingGenerators ψ n) (connectingGeneratorInclude ψ n)

/-- Generating sheaf of the previous free-forgetful iterate, used to extract constant
coefficients of degree-`n` standard-resolution terms. -/
def connectingPrevGenerators {B C : Sheaf J CommRingCat.{u}} (ψ : B ⟶ C) :
    ℕ → Sheaf J (Type u)
  | 0 => (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj C
  | n + 1 => connectingGenerators ψ n

/-- The zero assignment of a generating sheaf into the underlying type sheaf of `B`. -/
def connectingZeroAssign (B : Sheaf J CommRingCat.{u}) (E : Sheaf J (Type u)) :
    E ⟶ (sheafForget J).obj B :=
  InducedCategory.homMk
    { app := fun U => ↾fun _ => (0 : B.obj.obj U)
      naturality := fun _ _ _ => sorry }

/-- Constant-coefficient retraction of the degree-`n` `C/B` standard term onto `B`. -/
def connectingToBase {B C : Sheaf J CommRingCat.{u}} (ψ : B ⟶ C) :
    (n : ℕ) → {U : Dᵒᵖ} → (connectingGenerators ψ n).obj.obj U → B.obj.obj U
  | 0, U, y =>
      ((sheafForget J).map
          (CategoryTheory.Sheaf.FreeAlgebra.evaluation (Under.mk (𝟙 B))
            (connectingPrevGenerators ψ 0)
            (connectingZeroAssign B (connectingPrevGenerators ψ 0))).right).hom.app U y
  | n + 1, U, y =>
      ((sheafForget J).map
          (CategoryTheory.Sheaf.FreeAlgebra.evaluation (Under.mk (𝟙 B))
            (connectingGenerators ψ n)
            (connectingZeroAssign B (connectingGenerators ψ n))).right).hom.app U y

/-- Unfolding of `connectingToBase` in degree zero as forgetful evaluation of the free
`B`-algebra at the zero assignment. -/
theorem connectingToBase_zero_eq {B C : Sheaf J CommRingCat.{u}} (ψ : B ⟶ C)
    {U : Dᵒᵖ} (y : (connectingGenerators ψ 0).obj.obj U) :
    connectingToBase ψ 0 y =
      ((sheafForget J).map
          (CategoryTheory.Sheaf.FreeAlgebra.evaluation (Under.mk (𝟙 B))
            (connectingPrevGenerators ψ 0)
            (connectingZeroAssign B (connectingPrevGenerators ψ 0))).right).hom.app U y :=
  sorry

/-- Unfolding of `connectingToBase` in positive degree as forgetful evaluation of the free
`B`-algebra at the zero assignment. -/
theorem connectingToBase_succ_eq {B C : Sheaf J CommRingCat.{u}} (ψ : B ⟶ C)
    (n : ℕ) {U : Dᵒᵖ} (y : (connectingGenerators ψ (n + 1)).obj.obj U) :
    connectingToBase ψ (n + 1) y =
      ((sheafForget J).map
          (CategoryTheory.Sheaf.FreeAlgebra.evaluation (Under.mk (𝟙 B))
            (connectingGenerators ψ n)
            (connectingZeroAssign B (connectingGenerators ψ n))).right).hom.app U y :=
  sorry

/-- Image of a previous-iterate `C/B` element in the degree-`n` `B/A` standard-resolution
algebra, as the iterated free-forgetful unit of its constant `B`-coefficient. -/
def connectingGenerator {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : ℕ) {U : Dᵒᵖ} (y : (connectingGenerators ψ n).obj.obj U) :
    (standardTerm A (Under.mk φ) (op ⦋n⦌)).right.obj.obj U :=
  (Adjunction.unit.iterateApp (freeForgetAdjunction A) (Under.mk φ) n).hom.app U
    (connectingToBase ψ n y)

/-- Unfolding of `connectingGenerator` as `Adjunction.unit.iterateApp` of `connectingToBase`. -/
theorem connectingGenerator_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (ψ : B ⟶ C) (n : ℕ) {U : Dᵒᵖ} (y : (connectingGenerators ψ n).obj.obj U) :
    connectingGenerator φ ψ n y =
      (Adjunction.unit.iterateApp (freeForgetAdjunction A) (Under.mk φ) n).hom.app U
        (connectingToBase ψ n y) :=
  sorry

/-- The face `R_{n+1} ⟶ R_n` used to read a free generator of `R_{n+1}` as an element of the
previous iterate. -/
def connectingExtract {B C : Sheaf J CommRingCat.{u}} (ψ : B ⟶ C) (n : ℕ) :
    (standardTerm B (Under.mk ψ) (op ⦋n + 1⦌)).right ⟶
      (standardTerm B (Under.mk ψ) (op ⦋n⦌)).right :=
  (standardMap B (Under.mk ψ) (SimplexCategory.δ (0 : Fin (n + 2))).op).right

/-- Unfolding of `connectingExtract` as `standardMap` of `SimplexCategory.δ 0`. -/
theorem connectingExtract_eq {B C : Sheaf J CommRingCat.{u}} (ψ : B ⟶ C) (n : ℕ) :
    connectingExtract ψ n =
      (standardMap B (Under.mk ψ) (SimplexCategory.δ (0 : Fin (n + 2))).op).right :=
  sorry

/-- Image of `d(y)` in the degree-`n` term of `tensorCochain φ ψ`, obtained by extending
scalars of `d(connectingGenerator y)` along the degree-`n` augmentation and along `ψ`. -/
def connectingGeneratorValue {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : ℕ) {U : Dᵒᵖ} (y : (connectingGenerators ψ n).obj.obj U) :
    (connectingTarget φ ψ n).val.obj U :=
  ((extendRestrictAdj ψ).unit.app
      ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌))).val.app U
    (((extendRestrictAdj (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).unit.app
        (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom)).val.app U
      (((relativeDifferential (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom).app U).d
        (connectingGenerator φ ψ n y)))

/-- Unfolding of `connectingGeneratorValue` as the two `extendRestrictAdj` units applied to
`d(connectingGenerator y)`. -/
theorem connectingGeneratorValue_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (ψ : B ⟶ C) (n : ℕ) {U : Dᵒᵖ} (y : (connectingGenerators ψ n).obj.obj U) :
    connectingGeneratorValue φ ψ n y =
      ((extendRestrictAdj ψ).unit.app
          ((simplicialModule A (Under.mk φ)).obj (op ⦋n⦌))).val.app U
        (((extendRestrictAdj (standardAugmentation A (Under.mk φ) (op ⦋n⦌))).unit.app
            (relativeDifferentials (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom)).val.app U
          (((relativeDifferential (standardTerm A (Under.mk φ) (op ⦋n⦌)).hom).app U).d
            (connectingGenerator φ ψ n y))) :=
  sorry

/-- Image of a free generator of `R_{n+1}` in the previous iterate, obtained by including
the generator, evaluating the free `B`-algebra, and applying `connectingExtract`. -/
def connectingReadGenerator {B C : Sheaf J CommRingCat.{u}} (ψ : B ⟶ C) (n : ℕ)
    {U : Dᵒᵖ} (y : (connectingGenerators ψ n).obj.obj U) :
    (connectingGenerators ψ n).obj.obj U :=
  ConcreteCategory.hom ((connectingExtract ψ n).hom.app U)
    ((connectingGeneratorInclude ψ n ≫
        (sheafForget J).map (connectingFreeEval ψ n).right).hom.app U y)

/-- Unfolding of `connectingReadGenerator` through `FreeAlgebra.generator` and
`FreeAlgebra.evaluation`. -/
theorem connectingReadGenerator_eq {B C : Sheaf J CommRingCat.{u}} (ψ : B ⟶ C)
    (n : ℕ) {U : Dᵒᵖ} (y : (connectingGenerators ψ n).obj.obj U) :
    connectingReadGenerator ψ n y =
      ConcreteCategory.hom ((connectingExtract ψ n).hom.app U)
        ((connectingGeneratorInclude ψ n ≫
            (sheafForget J).map (connectingFreeEval ψ n).right).hom.app U y) :=
  sorry

/-- The `B`-relative derivation of `R_{n+1}` with values in `connectingTarget`, sending each
free generator `y` of the previous iterate to `connectingGeneratorValue y` after reading that
generator through `FreeAlgebra.generator` and `FreeAlgebra.evaluation`. -/
def connectingDerivation {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : ℕ) :
    SheafOfModules.RelativeDerivation
      (standardTerm B (Under.mk ψ) (op ⦋n + 1⦌)).hom (connectingTarget φ ψ n) :=
  PresheafOfModules.Derivation'.mk
    (fun U =>
      ModuleCat.Derivation.mk
        (fun r =>
          connectingGeneratorValue φ ψ n
            (connectingReadGenerator ψ n
              (ConcreteCategory.hom ((connectingExtract ψ n).hom.app U) r)))
        (fun _ _ => sorry) (fun _ _ => sorry) (fun _ => sorry))
    (fun _ _ _ _ => sorry)

/-- The Kähler-level transitivity boundary
`Ω_{R_{n+1}/B} ⟶ (Ω_{P_n/A} ⊗_B C)` restricted along the degree-`(n+1)` augmentation, as
universal descent of `connectingDerivation`. -/
def connectingKaehler {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    relativeDifferentials (standardTerm B (Under.mk ψ) (op ⦋n + 1⦌)).hom ⟶
      connectingTarget φ ψ n :=
  relativeDifferentialDesc (standardTerm B (Under.mk ψ) (op ⦋n + 1⦌)).hom
    (connectingDerivation φ ψ n)

/-- Native simplicial transitivity boundary
`Ω_{R_{n+1}/B} ⊗ C ⟶ (Ω_{P_n/A} ⊗ B) ⊗_B C`, as the adjunct of `connectingKaehler`. -/
def connectingSimplicialBoundary {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : ℕ) :
    (simplicialModule B (Under.mk ψ)).obj (op ⦋n + 1⦌) ⟶ tensorSimplicial φ ψ (op ⦋n⦌) :=
  ((extendRestrictAdj (standardAugmentation B (Under.mk ψ) (op ⦋n + 1⦌))).homEquiv _ _).symm
    (connectingKaehler φ ψ n)

/-- Degreewise transitivity boundary, nonzero only when the simplicial degrees differ by `1`. -/
def connectingSimplicialMap {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n m : ℕ) :
    (simplicialModule B (Under.mk ψ)).obj (op ⦋n⦌) ⟶ tensorSimplicial φ ψ (op ⦋m⦌) :=
  if h : n = m + 1 then
    eqToHom
        (congrArg (fun k : ℕ => (simplicialModule B (Under.mk ψ)).obj (op ⦋k⦌)) h) ≫
      connectingSimplicialBoundary φ ψ m
  else
    0

/-- The cochain-level components of the mapping-cone comparison, in every cohomological
degree. -/
def connectingPredMap {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) (i : ℤ) :
    L(ψ).X i ⟶ (tensorCochain φ ψ).X (i + 1) :=
  match hs : embeddingDownNat.r i, ht : embeddingDownNat.r (i + 1) with
  | some n, some m =>
      (extendXIso
          ((alternatingFaceMapComplex (SheafOfModules (ringSheaf J C))).obj
            (simplicialModule B (Under.mk ψ)))
          embeddingDownNat
          (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) hs)).hom ≫
        connectingSimplicialMap φ ψ n m ≫
        (extendAlong ψ).map
          (extendXIso
              ((alternatingFaceMapComplex (SheafOfModules (ringSheaf J B))).obj
                (simplicialModule A (Under.mk φ)))
              embeddingDownNat
              (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) ht)).inv
  | _, _ => 0

/-- Comparison of `L(ψ)` into the mapping cone of the first transitivity map. -/
def toMappingConeCochain {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    L(ψ) ⟶ mappingCone (tensorMapCochain φ ψ) where
  f i :=
    connectingPredMap φ ψ i ≫
      (mappingCone.inl (tensorMapCochain φ ψ)).v (i + 1) i (add_neg_cancel_right i 1)
  comm' := sorry

/-- Unfolding of `toMappingConeCochain` along `mappingCone.inl`. -/
theorem toMappingConeCochain_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (i : ℤ) :
    (toMappingConeCochain φ ψ).f i =
      connectingPredMap φ ψ i ≫
        (mappingCone.inl (tensorMapCochain φ ψ)).v (i + 1) i
          (add_neg_cancel_right i 1) :=
  sorry

/-- The connecting map `L(ψ) ⟶ (L(φ) ⊗^L_B C)⟦1⟧` of the transitivity triangle. -/
def connectingMap {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    DerivedCategory.Q.obj L(ψ) ⟶ (tensor φ ψ)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map (toMappingConeCochain φ ψ) ≫
    DerivedCategory.Q.map (mappingCone.triangle (tensorMapCochain φ ψ)).mor₃ ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (tensorCochain φ ψ)

/-- Unfolding of `connectingMap` as the mapping-cone comparison composed with
`mappingCone.triangle.mor₃` and `DerivedCategory.Q.commShiftIso 1`. -/
theorem connectingMap_eq {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    connectingMap φ ψ =
      DerivedCategory.Q.map (toMappingConeCochain φ ψ) ≫
        DerivedCategory.Q.map (mappingCone.triangle (tensorMapCochain φ ψ)).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (tensorCochain φ ψ) :=
  sorry

/-- The displayed transitivity triangle of sheaf cotangent complexes in `D(C)`. -/
def transitivityTriangle {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    Triangle (DerivedCategory (SheafOfModules (ringSheaf J C))) :=
  Triangle.mk (tensorMap φ ψ) (toRelativeMap φ ψ) (connectingMap φ ψ)

/-- The first vertex of `transitivityTriangle` is `tensor φ ψ`. -/
theorem transitivityTriangle_obj₁ {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (ψ : B ⟶ C) :
    (transitivityTriangle φ ψ).obj₁ = tensor φ ψ :=
  sorry

/-- The second vertex of `transitivityTriangle` is `Q.obj L(φ ≫ ψ)`. -/
theorem transitivityTriangle_obj₂ {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (ψ : B ⟶ C) :
    (transitivityTriangle φ ψ).obj₂ = DerivedCategory.Q.obj L(φ ≫ ψ) :=
  sorry

/-- The third vertex of `transitivityTriangle` is `Q.obj L(ψ)`. -/
theorem transitivityTriangle_obj₃ {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (ψ : B ⟶ C) :
    (transitivityTriangle φ ψ).obj₃ = DerivedCategory.Q.obj L(ψ) :=
  sorry

/-- The first morphism of `transitivityTriangle` is `tensorMap`. -/
theorem transitivityTriangle_mor₁ {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (ψ : B ⟶ C) :
    (transitivityTriangle φ ψ).mor₁ = tensorMap φ ψ :=
  sorry

/-- The second morphism of `transitivityTriangle` is `toRelativeMap`. -/
theorem transitivityTriangle_mor₂ {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (ψ : B ⟶ C) :
    (transitivityTriangle φ ψ).mor₂ = toRelativeMap φ ψ :=
  sorry

/-- The third morphism of `transitivityTriangle` is `connectingMap`. -/
theorem transitivityTriangle_mor₃ {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
    (ψ : B ⟶ C) :
    (transitivityTriangle φ ψ).mor₃ = connectingMap φ ψ :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex
