module

public import stacks_project.Chap85.Definition_85_13_1_System
public import stacks_project.Chap85.Lemma_85_12_4_Descent

/-!
# Cartesian derived systems from a coface cocycle

From `K_0` in `D(C_0)` and an isomorphism `α : f_{δ 1}⁻¹ K_0 ≅ f_{δ 0}⁻¹ K_0` in
`D(C_1)` satisfying the `C_2` cocycle, the vertex pullbacks
`K_n = f_{τ^n_n}⁻¹ K_0` and the source comparison maps `K_φ` assemble to a
cartesian simplicial system of the derived category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable {C : SimplexCategory → Type u} [∀ n, Category.{v} (C n)]
variable (J : ∀ n, GrothendieckTopology (C n))
variable (fInv : ∀ {m n : SimplexCategory}, (m ⟶ n) →
    Sheaf (J m) AddCommGrpCat.{w} ⥤ Sheaf (J n) AddCommGrpCat.{w})
variable [∀ n, HasSheafify (J n) AddCommGrpCat.{w}]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), (fInv φ).Additive]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), PreservesFiniteLimits (fInv φ)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), PreservesFiniteColimits (fInv φ)]
variable [functoriality : HasAbelianInverseImageFunctoriality J fInv]

/-- Reidentify `f_φ⁻¹` along an equality of simplex operators. -/
def recodeDerivedInverseImage {m n : SimplexCategory} {φ ψ : m ⟶ n} (h : φ = ψ) :
    derivedInverseImage J fInv φ ≅ derivedInverseImage J fInv ψ :=
  eqToIso (congrArg (fun t : m ⟶ n ↦ derivedInverseImage J fInv t) h)

/-- `recodeDerivedInverseImage` is the identity when the operator equality is `rfl`. -/
theorem recodeDerivedInverseImage_refl {m n : SimplexCategory} (φ : m ⟶ n) :
    recodeDerivedInverseImage J fInv (rfl : φ = φ) = Iso.refl _ :=
  sorry

/-- Canonical isomorphism `f_φ⁻¹ ∘ f_ψ⁻¹ ≅ f_{ψ ≫ φ}⁻¹` of derived inverse images,
from the underived identification `f_{ψ ≫ φ}⁻¹ ≅ f_ψ⁻¹ ⋙ f_φ⁻¹`. -/
def derivedInverseImageCompComparisonIso {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (hcomp : fInv (ψ ≫ φ) ≅ fInv ψ ⋙ fInv φ) :
    derivedInverseImage J fInv ψ ⋙ derivedInverseImage J fInv φ ≅
      derivedInverseImage J fInv (ψ ≫ φ) :=
  (derivedInverseImageCompFunctorIso J fInv ψ φ).symm ≪≫
    MapDerivedCategory.functorIso hcomp.symm

/-- The forward map of `derivedInverseImageCompComparisonIso` is
`derivedInverseImageCompComparisonOf`. -/
theorem derivedInverseImageCompComparisonIso_hom {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (hcomp : fInv (ψ ≫ φ) ≅ fInv ψ ⋙ fInv φ) :
    (derivedInverseImageCompComparisonIso J fInv ψ φ hcomp).hom =
      derivedInverseImageCompComparisonOf J fInv ψ φ hcomp :=
  sorry

/-- The pullback of `α` along a 2-face `δ i`, as a morphism in `D(C_2)`. -/
def derivedFacePullback (i : Fin 3)
    {K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w})}
    (α : (derivedInverseImage J fInv (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage J fInv (SimplexCategory.δ (0 : Fin 2))).obj K0) :
    (derivedInverseImage J fInv
        (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ i)).obj K0 ⟶
      (derivedInverseImage J fInv
        (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ i)).obj K0 :=
  (derivedInverseImageCompComparisonIso J fInv
      (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ i)
      (functoriality.pullbackCompIso (SimplexCategory.δ (1 : Fin 2))
        (SimplexCategory.δ i))).inv.app K0 ≫
    (derivedInverseImage J fInv (SimplexCategory.δ i)).map α.hom ≫
    (derivedInverseImageCompComparisonIso J fInv
      (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ i)
      (functoriality.pullbackCompIso (SimplexCategory.δ (0 : Fin 2))
        (SimplexCategory.δ i))).hom.app K0

/-- `derivedFacePullback i α` is `(f_{δ i})⁻¹ α` after the composition identifications. -/
theorem derivedFacePullback_eq (i : Fin 3)
    {K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w})}
    (α : (derivedInverseImage J fInv (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage J fInv (SimplexCategory.δ (0 : Fin 2))).obj K0) :
    derivedFacePullback J fInv i α =
      (derivedInverseImageCompComparisonIso J fInv
          (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ i)
          (functoriality.pullbackCompIso (SimplexCategory.δ (1 : Fin 2))
            (SimplexCategory.δ i))).inv.app K0 ≫
        (derivedInverseImage J fInv (SimplexCategory.δ i)).map α.hom ≫
        (derivedInverseImageCompComparisonIso J fInv
          (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ i)
          (functoriality.pullbackCompIso (SimplexCategory.δ (0 : Fin 2))
            (SimplexCategory.δ i))).hom.app K0 :=
  sorry

/-- `(f_{δ 1})⁻¹ α` transported to a morphism out of `(f_{δ 1 ≫ δ 2})⁻¹ K_0`. -/
def derivedCocycleLeft {K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w})}
    (α : (derivedInverseImage J fInv (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage J fInv (SimplexCategory.δ (0 : Fin 2))).obj K0) :
    (derivedInverseImage J fInv
        (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).obj K0 ⟶
      (derivedInverseImage J fInv
        (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).obj K0 :=
  (recodeDerivedInverseImage J fInv
      (SimplexCategory.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app K0 ≫
    derivedFacePullback J fInv 1 α

/-- `(f_{δ 0})⁻¹ α ∘ (f_{δ 2})⁻¹ α` after the `δ_comp_δ` identifications on `C_2`. -/
def derivedCocycleRight {K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w})}
    (α : (derivedInverseImage J fInv (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage J fInv (SimplexCategory.δ (0 : Fin 2))).obj K0) :
    (derivedInverseImage J fInv
        (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).obj K0 ⟶
      (derivedInverseImage J fInv
        (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).obj K0 :=
  derivedFacePullback J fInv 2 α ≫
    (recodeDerivedInverseImage J fInv
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
          (Fin.zero_le _))).hom.app K0 ≫
    derivedFacePullback J fInv 0 α ≫
    (recodeDerivedInverseImage J fInv
        (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
          le_rfl).symm).hom.app K0

/-- `derivedCocycleLeft` is `(f_{δ 1})⁻¹ α` after recoding along `δ_comp_δ_self`. -/
theorem derivedCocycleLeft_eq {K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w})}
    (α : (derivedInverseImage J fInv (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage J fInv (SimplexCategory.δ (0 : Fin 2))).obj K0) :
    derivedCocycleLeft J fInv α =
      (recodeDerivedInverseImage J fInv
          (SimplexCategory.δ_comp_δ_self (i := (1 : Fin 2))).symm).hom.app K0 ≫
        derivedFacePullback J fInv 1 α :=
  sorry

/-- `derivedCocycleRight` is `(f_{δ 0})⁻¹ α ∘ (f_{δ 2})⁻¹ α` after the `δ_comp_δ`
identifications. -/
theorem derivedCocycleRight_eq {K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w})}
    (α : (derivedInverseImage J fInv (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage J fInv (SimplexCategory.δ (0 : Fin 2))).obj K0) :
    derivedCocycleRight J fInv α =
      derivedFacePullback J fInv 2 α ≫
        (recodeDerivedInverseImage J fInv
            (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
              (Fin.zero_le _))).hom.app K0 ≫
        derivedFacePullback J fInv 0 α ≫
        (recodeDerivedInverseImage J fInv
            (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
              le_rfl).symm).hom.app K0 :=
  sorry

/-- The stage object `K_n = f_{τ^n_n}⁻¹ K_0`. -/
def ofCocycleObj (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (n : SimplexCategory) :
    DerivedCategory (Sheaf (J n) AddCommGrpCat.{w}) :=
  (derivedInverseImage J fInv (Sheaf.vertexOp n)).obj K0

/-- `ofCocycleObj K0 n` is the vertex pullback `f_{τ^n_n}⁻¹ K_0`. -/
theorem ofCocycleObj_eq (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (n : SimplexCategory) :
    ofCocycleObj J fInv K0 n =
      (derivedInverseImage J fInv (Sheaf.vertexOp n)).obj K0 :=
  sorry

/-- The source comparison isomorphism `K_φ : f_φ⁻¹ K_m ≅ K_n`, obtained by recoding along
`τ^m_m ≫ φ = τ^n_{φ(m)n}` and applying `(f_{τ^n_{φ(m)n}})⁻¹ α`. -/
def ofCocycleTransitionIso (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : (derivedInverseImage J fInv (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage J fInv (SimplexCategory.δ (0 : Fin 2))).obj K0)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (derivedInverseImage J fInv φ).obj (ofCocycleObj J fInv K0 m) ≅
      ofCocycleObj J fInv K0 n :=
  (derivedInverseImageCompComparisonIso J fInv (Sheaf.vertexOp m) φ
      (functoriality.pullbackCompIso (Sheaf.vertexOp m) φ)).app K0 ≪≫
    (recodeDerivedInverseImage J fInv
      (SimplexCategory.Hom.ext_zero_left (Sheaf.vertexOp m ≫ φ)
        (SimplexCategory.δ (1 : Fin 2) ≫ Sheaf.edgeOp φ))).app K0 ≪≫
    (derivedInverseImageCompComparisonIso J fInv
      (SimplexCategory.δ (1 : Fin 2)) (Sheaf.edgeOp φ)
      (functoriality.pullbackCompIso (SimplexCategory.δ (1 : Fin 2))
        (Sheaf.edgeOp φ))).symm.app K0 ≪≫
    (derivedInverseImage J fInv (Sheaf.edgeOp φ)).mapIso α ≪≫
    (derivedInverseImageCompComparisonIso J fInv
      (SimplexCategory.δ (0 : Fin 2)) (Sheaf.edgeOp φ)
      (functoriality.pullbackCompIso (SimplexCategory.δ (0 : Fin 2))
        (Sheaf.edgeOp φ))).app K0 ≪≫
    (recodeDerivedInverseImage J fInv
      (SimplexCategory.Hom.ext_zero_left
        (SimplexCategory.δ (0 : Fin 2) ≫ Sheaf.edgeOp φ)
        (Sheaf.vertexOp n))).app K0

/-- The forward map of `ofCocycleTransitionIso` is the source diagram for `K_φ`. -/
theorem ofCocycleTransitionIso_hom
    (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : (derivedInverseImage J fInv (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage J fInv (SimplexCategory.δ (0 : Fin 2))).obj K0)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (ofCocycleTransitionIso J fInv K0 α φ).hom =
      ((derivedInverseImageCompComparisonIso J fInv (Sheaf.vertexOp m) φ
          (functoriality.pullbackCompIso (Sheaf.vertexOp m) φ)).app K0 ≪≫
        (recodeDerivedInverseImage J fInv
          (SimplexCategory.Hom.ext_zero_left (Sheaf.vertexOp m ≫ φ)
            (SimplexCategory.δ (1 : Fin 2) ≫ Sheaf.edgeOp φ))).app K0 ≪≫
        (derivedInverseImageCompComparisonIso J fInv
          (SimplexCategory.δ (1 : Fin 2)) (Sheaf.edgeOp φ)
          (functoriality.pullbackCompIso (SimplexCategory.δ (1 : Fin 2))
            (Sheaf.edgeOp φ))).symm.app K0 ≪≫
        (derivedInverseImage J fInv (Sheaf.edgeOp φ)).mapIso α ≪≫
        (derivedInverseImageCompComparisonIso J fInv
          (SimplexCategory.δ (0 : Fin 2)) (Sheaf.edgeOp φ)
          (functoriality.pullbackCompIso (SimplexCategory.δ (0 : Fin 2))
            (Sheaf.edgeOp φ))).app K0 ≪≫
        (recodeDerivedInverseImage J fInv
          (SimplexCategory.Hom.ext_zero_left
            (SimplexCategory.δ (0 : Fin 2) ≫ Sheaf.edgeOp φ)
            (Sheaf.vertexOp n))).app K0).hom :=
  sorry

/-- The identity operator acts on the cocycle system by the canonical identity comparison. -/
theorem ofCocycle_map_id (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : (derivedInverseImage J fInv (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage J fInv (SimplexCategory.δ (0 : Fin 2))).obj K0)
    (h : derivedCocycleLeft J fInv α = derivedCocycleRight J fInv α)
    (n : SimplexCategory) :
    (derivedInverseImageIdComparisonOf J fInv (functoriality.pullbackIdIso n)).app
        (ofCocycleObj J fInv K0 n) ≫
      (ofCocycleTransitionIso J fInv K0 α (𝟙 n)).hom =
      𝟙 (ofCocycleObj J fInv K0 n) :=
  sorry

/-- Transitions of the cocycle system respect composition of simplex operators after the
canonical comparison `f_φ⁻¹ ∘ f_ψ⁻¹ ⟶ f_{ψ ≫ φ}⁻¹`. -/
theorem ofCocycle_map_comp (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : (derivedInverseImage J fInv (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage J fInv (SimplexCategory.δ (0 : Fin 2))).obj K0)
    (h : derivedCocycleLeft J fInv α = derivedCocycleRight J fInv α)
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (derivedInverseImageCompComparisonOf J fInv ψ φ
        (functoriality.pullbackCompIso ψ φ)).app (ofCocycleObj J fInv K0 l) ≫
      (ofCocycleTransitionIso J fInv K0 α (ψ ≫ φ)).hom =
      (fInv φ).mapDerivedCategory.map (ofCocycleTransitionIso J fInv K0 α ψ).hom ≫
        (ofCocycleTransitionIso J fInv K0 α φ).hom :=
  sorry

/-- The simplicial system `(K_n, K_φ)` of the derived category assembled from
`K_0` in `D(C_0)` and an isomorphism `α : f_{δ 1}⁻¹ K_0 ≅ f_{δ 0}⁻¹ K_0` in
`D(C_1)` satisfying the `C_2` cocycle `derivedCocycleLeft α = derivedCocycleRight α`,
with `K_n = f_{τ^n_n}⁻¹ K_0`. -/
def ofCocycle (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : (derivedInverseImage J fInv (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage J fInv (SimplexCategory.δ (0 : Fin 2))).obj K0)
    (h : derivedCocycleLeft J fInv α = derivedCocycleRight J fInv α) :
    DerivedAbelianSystem J fInv :=
  DerivedAbelianSystem.of (ofCocycleObj J fInv K0)
    (fun φ ↦ (ofCocycleTransitionIso J fInv K0 α φ).hom)
    (ofCocycle_map_id J fInv K0 α h) (ofCocycle_map_comp J fInv K0 α h)

/-- The stage object of `ofCocycle` at `n` is `K_n = f_{τ^n_n}⁻¹ K_0`. -/
theorem ofCocycle_obj (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : (derivedInverseImage J fInv (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage J fInv (SimplexCategory.δ (0 : Fin 2))).obj K0)
    (h : derivedCocycleLeft J fInv α = derivedCocycleRight J fInv α)
    (n : SimplexCategory) :
    (ofCocycle J fInv K0 α h).obj n = ofCocycleObj J fInv K0 n :=
  sorry

/-- The transition of `ofCocycle` at `φ` is the source comparison `K_φ`. -/
theorem ofCocycle_map (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : (derivedInverseImage J fInv (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage J fInv (SimplexCategory.δ (0 : Fin 2))).obj K0)
    (h : derivedCocycleLeft J fInv α = derivedCocycleRight J fInv α)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (ofCocycle J fInv K0 α h).map φ = (ofCocycleTransitionIso J fInv K0 α φ).hom :=
  sorry

/-- The system constructed from `(K_0, α)` is cartesian: every `K_φ` is an isomorphism. -/
instance ofCocycle_isCartesian
    (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : (derivedInverseImage J fInv (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage J fInv (SimplexCategory.δ (0 : Fin 2))).obj K0)
    (h : derivedCocycleLeft J fInv α = derivedCocycleRight J fInv α) :
    DerivedAbelianSystem.IsCartesian (ofCocycle J fInv K0 α h) where
  isIso_map := sorry

section OnComponents

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), (abelianInverseImage C J φ).Additive]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n), PreservesFiniteLimits (abelianInverseImage C J φ)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    PreservesFiniteColimits (abelianInverseImage C J φ)]

/-- Case A of Situation 85.3.3: the cartesian derived system on component sites assembled
from `K_0` and a coface cocycle, using `abelianInverseImage`. -/
def ofCocycleOnComponents
    (K0 : DerivedCategory (Sheaf (J ⦋0⦌).toGrothendieck AddCommGrpCat.{w}))
    (α : (derivedInverseImage (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ abelianInverseImage C J φ)
        (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ abelianInverseImage C J φ)
        (SimplexCategory.δ (0 : Fin 2))).obj K0)
    (h : derivedCocycleLeft (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ abelianInverseImage C J φ) α =
      derivedCocycleRight (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ abelianInverseImage C J φ) α) :
    DerivedAbelianSystemOnComponents C J :=
  ofCocycle (fun n ↦ (J n).toGrothendieck) (fun φ ↦ abelianInverseImage C J φ) K0 α h

/-- `ofCocycleOnComponents` is `ofCocycle` for `abelianInverseImage` on component sites. -/
theorem ofCocycleOnComponents_eq
    (K0 : DerivedCategory (Sheaf (J ⦋0⦌).toGrothendieck AddCommGrpCat.{w}))
    (α : (derivedInverseImage (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ abelianInverseImage C J φ)
        (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ abelianInverseImage C J φ)
        (SimplexCategory.δ (0 : Fin 2))).obj K0)
    (h : derivedCocycleLeft (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ abelianInverseImage C J φ) α =
      derivedCocycleRight (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ abelianInverseImage C J φ) α) :
    ofCocycleOnComponents C J K0 α h =
      ofCocycle (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ abelianInverseImage C J φ) K0 α h :=
  sorry

/-- The case A specialization of `ofCocycle` is cartesian. -/
instance ofCocycleOnComponents_isCartesian
    (K0 : DerivedCategory (Sheaf (J ⦋0⦌).toGrothendieck AddCommGrpCat.{w}))
    (α : (derivedInverseImage (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ abelianInverseImage C J φ)
        (SimplexCategory.δ (1 : Fin 2))).obj K0 ≅
      (derivedInverseImage (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ abelianInverseImage C J φ)
        (SimplexCategory.δ (0 : Fin 2))).obj K0)
    (h : derivedCocycleLeft (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ abelianInverseImage C J φ) α =
      derivedCocycleRight (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ abelianInverseImage C J φ) α) :
    DerivedAbelianSystem.IsCartesian (ofCocycleOnComponents C J K0 α h) :=
  ofCocycle_isCartesian (fun n ↦ (J n).toGrothendieck)
    (fun φ ↦ abelianInverseImage C J φ) K0 α h

end OnComponents

end CategoryTheory.SimplicialSites
