module

public import ReasLib.RingTheory.CotangentComplex.Functoriality
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.ExtraDegeneracy
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transitivity of cotangent complexes

For compatible commutative algebras `A → B → C`, the canonical cotangent maps form a
triangle in the derived category of `C`-modules. Its first vertex is the derived scalar
extension of the cotangent complex of `B` over `A`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex Opposite AlgebraicTopology ComplexShape
open CochainComplex CochainComplex.HomComplex
open CommRingCat.Under.FreeAlgebra CommRingCat.Under.CotangentComplex
open scoped Simplicial CategoryTheory.IteratedEndofunctor

noncomputable section

universe u

namespace Algebra.CotangentComplex

/-- The cotangent complex `L_{B/A}` as an object of `D(Mod B)`. -/
abbrev derived (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    DerivedCategory (ModuleCat.{u} B) :=
  DerivedCategory.Q.obj (Algebra.cotangentComplex A B)

/-- Cochain-level extension of scalars of `Algebra.cotangentComplex A B` along `B → C`. -/
abbrev tensorCochain (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    CochainComplex (ModuleCat.{u} C) ℤ :=
  ((ModuleCat.extendScalars (algebraMap B C)).mapHomologicalComplex (up ℤ)).obj
    (Algebra.cotangentComplex A B)

/-- The localization of the scalar-extended standard cotangent complex. -/
abbrev tensor (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    DerivedCategory (ModuleCat.{u} C) :=
  DerivedCategory.Q.obj (tensorCochain A B C)

/-- Derived-functor form of `tensor`, as `derivedExtensionOfScalars` of `derived A B`. -/
abbrev tensorDerived (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    DerivedCategory (ModuleCat.{u} C) :=
  (ModuleCat.derivedExtensionOfScalars (algebraMap B C)).obj (derived A B)

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

/-- The second map `L_{C/A} ⟶ L_{C/B}` of the transitivity triangle in `D(C)`. -/
def toRelativeMap (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    derived A C ⟶ derived B C :=
  DerivedCategory.Q.map (toRelativeMapCochain A B C)

/-- The simplicial `C`-module in degree `n` underlying `tensorCochain A B C`. -/
private abbrev tensorSimplicial (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (n : SimplexCategoryᵒᵖ) : ModuleCat.{u} C :=
  (ModuleCat.extendScalars (algebraMap B C)).obj
    ((simplicialModule (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).obj n)

/-- The initial algebra maps to its free-algebra comonad image. -/
private def initialCoalgebra (B : CommRingCat.{u}) :
    Under.mk (𝟙 B) ⟶ (comonadFunctor B).obj (Under.mk (𝟙 B)) :=
  Under.homMk ((comonadFunctor B).obj (Under.mk (𝟙 B))).hom

private def initialCounitSplit (B : CommRingCat.{u}) :
    SplitEpi ((CommRingCat.Under.PolynomialResolution.comonad B).ε.app
      (Under.mk (𝟙 B))) where
  section_ := initialCoalgebra B
  id := (Under.mkIdInitial (X := B)).hom_ext _ _

/-- Inserting the initial-algebra coalgebra contracts its standard resolution. -/
private def initialExtraDegeneracy (B : CommRingCat.{u}) (n : ℕ) :
    standardTerm B (Under.mk (𝟙 B)) (op ⦋n⦌) ⟶
      standardTerm B (Under.mk (𝟙 B)) (op ⦋n + 1⦌) :=
  (Endofunctor.iterate (comonadFunctor B) (n + 1)).map (initialCoalgebra B) ≫
    (IteratedEndofunctor.prependIso (comonadFunctor B) n).hom.app (Under.mk (𝟙 B))

private theorem initialExtraDegeneracy_comp_augmentation (B : CommRingCat.{u}) (n : ℕ) :
    (initialExtraDegeneracy B n).right ≫
        standardAugmentation B (Under.mk (𝟙 B)) (op ⦋n + 1⦌) =
      standardAugmentation B (Under.mk (𝟙 B)) (op ⦋n⦌) := by
  let X := (CommRingCat.Under.PolynomialResolution.evaluation B).obj (Under.mk (𝟙 B))
  have hs : initialExtraDegeneracy B n ≫ X.left.δ 0 = 𝟙 _ :=
    Comonad.simplicialResolution.eval.splitCounit.s_comp_δ₀ (initialCounitSplit B) n
  have hn := X.hom.naturality (SimplexCategory.δ (0 : Fin (n + 2))).op
  change X.left.δ 0 ≫ X.hom.app (op ⦋n⦌) =
    X.hom.app (op ⦋n + 1⦌) ≫ 𝟙 _ at hn
  have hn' : X.hom.app (op ⦋n + 1⦌) = X.left.δ 0 ≫ X.hom.app (op ⦋n⦌) :=
    (hn.trans (Category.comp_id _)).symm
  have h : initialExtraDegeneracy B n ≫ X.hom.app (op ⦋n + 1⦌) =
      X.hom.app (op ⦋n⦌) := calc
    _ = initialExtraDegeneracy B n ≫ (X.left.δ 0 ≫ X.hom.app (op ⦋n⦌)) :=
      congrArg (fun f => initialExtraDegeneracy B n ≫ f) hn'
    _ = (initialExtraDegeneracy B n ≫ X.left.δ 0) ≫ X.hom.app (op ⦋n⦌) :=
      (Category.assoc _ _ _).symm
    _ = X.hom.app (op ⦋n⦌) := by rw [hs, Category.id_comp]
  exact congrArg (fun f => f.right) h

/-- The standard-resolution prism factors through the contracted initial target algebra. -/
private def resolutionPrism (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    (standardTerm (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) (op ⦋n⦌)).right ⟶
    (standardTerm (CommRingCat.of B)
      (Under.mk (CommRingCat.ofHom (algebraMap B C))) (op ⦋n + 1⦌)).right :=
  standardTermRightHom (B := Under.mk (CommRingCat.ofHom (algebraMap A B)))
    (B' := Under.mk (𝟙 (CommRingCat.of B)))
    (CommRingCat.ofHom (algebraMap A B)) (𝟙 (CommRingCat.of B)) (op ⦋n⦌) ≫
  (initialExtraDegeneracy (CommRingCat.of B) n).right ≫
  (((CommRingCat.Under.PolynomialResolution.evaluation (CommRingCat.of B)).map
    (Under.homMk (CommRingCat.ofHom (algebraMap B C)) :
      Under.mk (𝟙 (CommRingCat.of B)) ⟶
        Under.mk (CommRingCat.ofHom (algebraMap B C)))).left.app (op ⦋n + 1⦌)).right

private theorem resolutionPrism_square (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    CommRingCat.ofHom (algebraMap A B) ≫
      (standardTerm (CommRingCat.of B)
        (Under.mk (CommRingCat.ofHom (algebraMap B C))) (op ⦋n + 1⦌)).hom =
    (standardTerm (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) (op ⦋n⦌)).hom ≫
      resolutionPrism A B C n := by
  dsimp only [resolutionPrism]
  rw [← Category.assoc, ← Category.assoc,
    ← standardTermRightHom_square _ _ (by rfl) (op ⦋n⦌)]
  simp only [Category.assoc, Under.w]

private theorem resolutionPrism_comp_augmentation (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    (algebraMap B C).comp
      (standardAugmentation (CommRingCat.of A)
        (Under.mk (CommRingCat.ofHom (algebraMap A B))) (op ⦋n⦌)).hom =
    (standardAugmentation (CommRingCat.of B)
      (Under.mk (CommRingCat.ofHom (algebraMap B C))) (op ⦋n + 1⦌)).hom.comp
        (resolutionPrism A B C n).hom := by
  let f : Under.mk (𝟙 (CommRingCat.of B)) ⟶
      Under.mk (CommRingCat.ofHom (algebraMap B C)) :=
    Under.homMk (CommRingCat.ofHom (algebraMap B C))
  let F := CommRingCat.Under.PolynomialResolution.evaluation (CommRingCat.of B)
  have hm := (F.map f).w
  have hma := congrArg (fun t => (t.app (op ⦋n + 1⦌)).right) hm
  change ((F.map f).left.app (op ⦋n + 1⦌)).right ≫
      standardAugmentation (CommRingCat.of B)
        (Under.mk (CommRingCat.ofHom (algebraMap B C))) (op ⦋n + 1⦌) =
    standardAugmentation (CommRingCat.of B)
      (Under.mk (𝟙 (CommRingCat.of B))) (op ⦋n + 1⦌) ≫
      ((F.map f).right).right at hma
  have hfr : ((F.map f).right).right = CommRingCat.ofHom (algebraMap B C) :=
    congrArg (fun t => t.right)
      (Comonad.simplicialResolution.eval.map.right
        (CommRingCat.Under.PolynomialResolution.comonad (CommRingCat.of B)) f)
  rw [hfr] at hma
  have he := initialExtraDegeneracy_comp_augmentation (CommRingCat.of B) n
  have hf := standardTermRightHom_comp_augmentation
    (B := Under.mk (CommRingCat.ofHom (algebraMap A B)))
    (B' := Under.mk (𝟙 (CommRingCat.of B)))
    (CommRingCat.ofHom (algebraMap A B)) (𝟙 (CommRingCat.of B)) (by rfl) (op ⦋n⦌)
  let g := standardTermRightHom
    (B := Under.mk (CommRingCat.ofHom (algebraMap A B)))
    (B' := Under.mk (𝟙 (CommRingCat.of B)))
    (CommRingCat.ofHom (algebraMap A B)) (𝟙 (CommRingCat.of B)) (op ⦋n⦌)
  let e := (initialExtraDegeneracy (CommRingCat.of B) n).right
  let t := ((F.map f).left.app (op ⦋n + 1⦌)).right
  let a₀ := standardAugmentation (CommRingCat.of B)
    (Under.mk (𝟙 (CommRingCat.of B))) (op ⦋n⦌)
  let a₁ := standardAugmentation (CommRingCat.of B)
    (Under.mk (𝟙 (CommRingCat.of B))) (op ⦋n + 1⦌)
  let a₂ := standardAugmentation (CommRingCat.of B)
    (Under.mk (CommRingCat.ofHom (algebraMap B C))) (op ⦋n + 1⦌)
  let β := CommRingCat.ofHom (algebraMap B C)
  have hg : standardAugmentation (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) (op ⦋n⦌) = g ≫ a₀ := by
    apply CommRingCat.hom_ext
    exact (RingHom.id_comp _).symm.trans hf
  have ht : (e ≫ t) ≫ a₂ = a₀ ≫ β := calc
    _ = e ≫ (t ≫ a₂) := Category.assoc _ _ _
    _ = e ≫ (a₁ ≫ β) := congrArg (fun k => e ≫ k) hma
    _ = (e ≫ a₁) ≫ β := (Category.assoc _ _ _).symm
    _ = a₀ ≫ β := congrArg (fun k => k ≫ β) he
  have hc : standardAugmentation (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) (op ⦋n⦌) ≫ β =
      resolutionPrism A B C n ≫ a₂ := calc
    _ = (g ≫ a₀) ≫ β := congrArg (fun k => k ≫ β) hg
    _ = g ≫ (a₀ ≫ β) := Category.assoc _ _ _
    _ = g ≫ ((e ≫ t) ≫ a₂) := congrArg (fun k => g ≫ k) ht.symm
    _ = (g ≫ (e ≫ t)) ≫ a₂ := (Category.assoc _ _ _).symm
  exact congrArg (fun k => k.hom) hc

/-- The prism on relative differentials is augmented and extended to the final ring. -/
private def prismModule (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (n : ℕ) :
    tensorSimplicial A B C (op ⦋n⦌) ⟶
      (simplicialModule (CommRingCat.of B)
        (Under.mk (CommRingCat.ofHom (algebraMap B C)))).obj (op ⦋n + 1⦌) :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap B C)).homEquiv _ _).symm
    (((ModuleCat.extendRestrictScalarsAdj
      (standardAugmentation (CommRingCat.of A)
        (Under.mk (CommRingCat.ofHom (algebraMap A B))) (op ⦋n⦌)).hom).homEquiv _ _).symm
      (CommRingCat.KaehlerDifferential.map (resolutionPrism_square A B C n) ≫
        (ModuleCat.restrictScalars (resolutionPrism A B C n).hom).map
          ((ModuleCat.extendRestrictScalarsAdj
            (standardAugmentation (CommRingCat.of B)
              (Under.mk (CommRingCat.ofHom (algebraMap B C))) (op ⦋n + 1⦌)).hom).unit.app _) ≫
        (ModuleCat.restrictScalarsComp' (resolutionPrism A B C n).hom
          (standardAugmentation (CommRingCat.of B)
            (Under.mk (CommRingCat.ofHom (algebraMap B C))) (op ⦋n + 1⦌)).hom
          ((algebraMap B C).comp
            (standardAugmentation (CommRingCat.of A)
              (Under.mk (CommRingCat.ofHom (algebraMap A B))) (op ⦋n⦌)).hom)
          (resolutionPrism_comp_augmentation A B C n)).inv.app _))

/-- The degree-minus-one cochain induced by the standard-resolution prism. -/
@[no_expose] def transitivityNullhomotopy (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    Cochain (tensorCochain A B C) (Algebra.cotangentComplex B C) (-1) :=
  Cochain.mk fun i j _ =>
    match hi : embeddingDownNat.r i, hj : embeddingDownNat.r j with
    | some n, some m =>
      if h : n + 1 = m then
        (ModuleCat.extendScalars (algebraMap B C)).map
          (extendXIso
            ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
              (simplicialModule (CommRingCat.of A)
                (Under.mk (CommRingCat.ofHom (algebraMap A B))))) embeddingDownNat
            (embeddingDownNat.f_eq_of_r_eq_some hi)).hom ≫
        prismModule A B C n ≫
        eqToHom (congrArg (fun k : ℕ =>
          (simplicialModule (CommRingCat.of B)
            (Under.mk (CommRingCat.ofHom (algebraMap B C)))).obj (op ⦋k⦌)) h) ≫
        (extendXIso
          ((alternatingFaceMapComplex (ModuleCat.{u} C)).obj
            (simplicialModule (CommRingCat.of B)
              (Under.mk (CommRingCat.ofHom (algebraMap B C))))) embeddingDownNat
          (embeddingDownNat.f_eq_of_r_eq_some hj)).inv
      else 0
    | _, _ => 0

/-- The differential of the prism cochain is the composite of the canonical cotangent maps. -/
theorem transitivityNullhomotopy_eq (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    δ (-1) 0 (transitivityNullhomotopy A B C) =
      Cochain.ofHom (tensorMapCochain A B C ≫ toRelativeMapCochain A B C) := by
  sorry

/-- The cone of the first cotangent map maps canonically to the relative cotangent complex. -/
def fromMappingConeCochain (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    mappingCone (tensorMapCochain A B C) ⟶ Algebra.cotangentComplex B C :=
  mappingCone.desc (tensorMapCochain A B C) (transitivityNullhomotopy A B C)
    (toRelativeMapCochain A B C) (transitivityNullhomotopy_eq A B C)

/-- The canonical cotangent cone comparison is a quasi-isomorphism. -/
instance fromMappingConeCochain_quasiIso (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    QuasiIso (fromMappingConeCochain A B C) := by
  sorry

/-- The derived counit compares derived scalar extension with the scalar-extended complex. -/
def tensorComparison (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    tensorDerived A B C ⟶ tensor A B C :=
  (ModuleCat.derivedExtensionComplexCounit (algebraMap B C)).app (Algebra.cotangentComplex A B)

/-- The standard cotangent complex computes derived extension of scalars. -/
instance tensorComparison_isIso (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    IsIso (tensorComparison A B C) := by
  sorry

/-- Derived scalar extension of the cotangent complex is represented by its standard complex. -/
def tensorDerivedIso (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    tensorDerived A B C ≅ tensor A B C :=
  asIso (tensorComparison A B C)

/-- The transitivity boundary is the cone boundary after inverting the localized comparison. -/
def connectingMap (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    derived B C ⟶ (tensor A B C)⟦(1 : ℤ)⟧ :=
  inv (DerivedCategory.Q.map (fromMappingConeCochain A B C)) ≫
    DerivedCategory.Q.map (mappingCone.triangle (tensorMapCochain A B C)).mor₃ ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (tensorCochain A B C)

/-- The transitivity boundary is the inverse cone comparison followed by the localized boundary. -/
theorem connectingMap_eq (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    connectingMap A B C =
      inv (DerivedCategory.Q.map (fromMappingConeCochain A B C)) ≫
        DerivedCategory.Q.map (mappingCone.triangle (tensorMapCochain A B C)).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (tensorCochain A B C) := by
  rfl

/-- The displayed transitivity triangle of cotangent complexes in `D(C)`. -/
def transitivityTriangle (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    Triangle (DerivedCategory (ModuleCat.{u} C)) :=
  Triangle.mk (tensorMap A B C) (toRelativeMap A B C) (connectingMap A B C)

/-- The first vertex of `transitivityTriangle` is `tensor A B C`. -/
theorem transitivityTriangle_obj₁ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (transitivityTriangle A B C).obj₁ = tensor A B C := by
  rfl

/-- The second vertex of `transitivityTriangle` is `derived A C`. -/
theorem transitivityTriangle_obj₂ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (transitivityTriangle A B C).obj₂ = derived A C := by
  rfl

/-- The third vertex of `transitivityTriangle` is `derived B C`. -/
theorem transitivityTriangle_obj₃ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (transitivityTriangle A B C).obj₃ = derived B C := by
  rfl

/-- The first morphism of `transitivityTriangle` is `tensorMap`. -/
theorem transitivityTriangle_mor₁ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (transitivityTriangle A B C).mor₁ = tensorMap A B C := by
  rfl

/-- The second morphism of `transitivityTriangle` is `toRelativeMap`. -/
theorem transitivityTriangle_mor₂ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (transitivityTriangle A B C).mor₂ = toRelativeMap A B C := by
  rfl

/-- The third morphism of `transitivityTriangle` is `connectingMap`. -/
theorem transitivityTriangle_mor₃ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (transitivityTriangle A B C).mor₃ = connectingMap A B C := by
  rfl

/-- The transitivity triangle of cotangent complexes is distinguished in `D(C)`. -/
theorem transitivityTriangle_distinguished (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    transitivityTriangle A B C ∈ distTriang (DerivedCategory (ModuleCat.{u} C)) :=
  sorry

/-- If the relative cotangent complex of `C` over `B` vanishes, the canonical map
from the derived scalar extension of the cotangent complex of `B` over `A` to
the cotangent complex of `C` over `A` is an isomorphism. -/
@[stacks 08R3]
theorem tensorMap_isIso_of_isZero (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (h_zero : IsZero (derived B C)) : IsIso (tensorMap A B C) :=
  sorry

/-- The first transitivity map `tensorMap A B C` is an isomorphism if and only if
`derived B C` vanishes. -/
theorem isIso_tensorMap_iff_isZero_derived (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    IsIso (tensorMap A B C) ↔ IsZero (derived B C) :=
  sorry

/-- Vanishing of the relative cotangent complex makes the first transitivity map
an isomorphism. -/
instance tensorMap_isIso_of_fact_isZero (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Fact (IsZero (derived B C))] : IsIso (tensorMap A B C) :=
  tensorMap_isIso_of_isZero A B C Fact.out

end Algebra.CotangentComplex
