/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.DerivedSystem
public import ReasLib.CategoryTheory.Sites.Simplicial.FaceDescent

/-!
# Cartesian derived systems from a coface cocycle

From `K_0` in `D(C_0)` and an isomorphism `α : f_{δ 1}⁻¹ K_0 ≅ f_{δ 0}⁻¹ K_0` in
`D(C_1)` satisfying the `C_2` cocycle, the vertex pullbacks
`K_n = f_{τ^n_n}⁻¹ K_0` and the edge-pullback transition maps `K_φ` assemble to a
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
variable (compIso : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
    fInv (ψ ≫ φ) ≅ fInv ψ ⋙ fInv φ)

namespace DerivedSystem

/-- The derived composition comparisons satisfy the associativity equation, including
transport between the two parenthesizations of a composite simplex operator. -/
def IsAssociative : Prop :=
  ∀ {k l m n : SimplexCategory} (ψ : k ⟶ l) (φ : l ⟶ m) (χ : m ⟶ n),
    (derivedInverseImageCompIso J fInv (ψ ≫ φ) χ (compIso (ψ ≫ φ) χ)).hom ≫
        whiskerRight (derivedInverseImageCompIso J fInv ψ φ (compIso ψ φ)).hom
          (fInv χ).mapDerivedCategory ≫
        (Functor.associator (fInv ψ).mapDerivedCategory (fInv φ).mapDerivedCategory
          (fInv χ).mapDerivedCategory).hom =
      (eqToIso (congrArg (fun t : k ⟶ n ↦ (fInv t).mapDerivedCategory)
        (Category.assoc ψ φ χ))).hom ≫
        (derivedInverseImageCompIso J fInv ψ (φ ≫ χ) (compIso ψ (φ ≫ χ))).hom ≫
        whiskerLeft (fInv ψ).mapDerivedCategory
          (derivedInverseImageCompIso J fInv φ χ (compIso φ χ)).hom

/-- Coherence of the abelian inverse images passes to their canonical exact
derived functors. -/
theorem isAssociative_of_context
    (context : IsInverseImageContext J fInv compIso) :
    IsAssociative J fInv compIso := sorry

/-- The pullback of `α` along a 2-face `δ i`, as a morphism in `D(C_2)`. -/
def facePullback (i : Fin 3)
    {K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w})}
    (α : ((fInv (SimplexCategory.δ (1 : Fin 2))).mapDerivedCategory).obj K0 ≅
      ((fInv (SimplexCategory.δ (0 : Fin 2))).mapDerivedCategory).obj K0) :
    ((fInv (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ i)).mapDerivedCategory).obj K0 ⟶
      ((fInv (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ i)).mapDerivedCategory).obj K0 :=
  (derivedInverseImageCompIso J fInv
      (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ i)
      (compIso (SimplexCategory.δ (1 : Fin 2))
        (SimplexCategory.δ i))).hom.app K0 ≫
    ((fInv (SimplexCategory.δ i)).mapDerivedCategory).map α.hom ≫
    (derivedInverseImageCompIso J fInv
      (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ i)
      (compIso (SimplexCategory.δ (0 : Fin 2))
        (SimplexCategory.δ i))).inv.app K0

/-- `facePullback i α` is `(f_{δ i})⁻¹ α` after the composition identifications. -/
theorem facePullback_eq (i : Fin 3)
    {K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w})}
    (α : ((fInv (SimplexCategory.δ (1 : Fin 2))).mapDerivedCategory).obj K0 ≅
      ((fInv (SimplexCategory.δ (0 : Fin 2))).mapDerivedCategory).obj K0) :
    facePullback J fInv compIso i α =
      (derivedInverseImageCompIso J fInv
          (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ i)
          (compIso (SimplexCategory.δ (1 : Fin 2))
            (SimplexCategory.δ i))).hom.app K0 ≫
        ((fInv (SimplexCategory.δ i)).mapDerivedCategory).map α.hom ≫
        (derivedInverseImageCompIso J fInv
          (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ i)
          (compIso (SimplexCategory.δ (0 : Fin 2))
            (SimplexCategory.δ i))).inv.app K0 :=
  rfl

/-- `(f_{δ 1})⁻¹ α` transported to a morphism out of `(f_{δ 1 ≫ δ 2})⁻¹ K_0`. -/
def cocycleLeft {K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w})}
    (α : ((fInv (SimplexCategory.δ (1 : Fin 2))).mapDerivedCategory).obj K0 ≅
      ((fInv (SimplexCategory.δ (0 : Fin 2))).mapDerivedCategory).obj K0) :
    ((fInv (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).mapDerivedCategory).obj K0 ⟶
      ((fInv (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).mapDerivedCategory).obj K0 :=
  (eqToIso (congrArg (fun t ↦ (fInv t).mapDerivedCategory) (SimplexCategory.δ_comp_δ_self (i := (1 : Fin 2))).symm)).hom.app K0 ≫
    facePullback J fInv compIso 1 α

/-- `(f_{δ 0})⁻¹ α ∘ (f_{δ 2})⁻¹ α` after the `δ_comp_δ` identifications on `C_2`. -/
def cocycleRight {K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w})}
    (α : ((fInv (SimplexCategory.δ (1 : Fin 2))).mapDerivedCategory).obj K0 ≅
      ((fInv (SimplexCategory.δ (0 : Fin 2))).mapDerivedCategory).obj K0) :
    ((fInv (SimplexCategory.δ (1 : Fin 2) ≫ SimplexCategory.δ (2 : Fin 3))).mapDerivedCategory).obj K0 ⟶
      ((fInv (SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (1 : Fin 3))).mapDerivedCategory).obj K0 :=
  facePullback J fInv compIso 2 α ≫
    (eqToIso (congrArg (fun t ↦ (fInv t).mapDerivedCategory) (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
          (Fin.zero_le _)))).hom.app K0 ≫
    facePullback J fInv compIso 0 α ≫
    (eqToIso (congrArg (fun t ↦ (fInv t).mapDerivedCategory) (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
          le_rfl).symm)).hom.app K0

/-- `cocycleLeft` is `(f_{δ 1})⁻¹ α` after recoding along `δ_comp_δ_self`. -/
theorem cocycleLeft_eq {K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w})}
    (α : ((fInv (SimplexCategory.δ (1 : Fin 2))).mapDerivedCategory).obj K0 ≅
      ((fInv (SimplexCategory.δ (0 : Fin 2))).mapDerivedCategory).obj K0) :
    cocycleLeft J fInv compIso α =
      (eqToIso (congrArg (fun t ↦ (fInv t).mapDerivedCategory) (SimplexCategory.δ_comp_δ_self (i := (1 : Fin 2))).symm)).hom.app K0 ≫
        facePullback J fInv compIso 1 α :=
  rfl

/-- `cocycleRight` is `(f_{δ 0})⁻¹ α ∘ (f_{δ 2})⁻¹ α` after the `δ_comp_δ`
identifications. -/
theorem cocycleRight_eq {K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w})}
    (α : ((fInv (SimplexCategory.δ (1 : Fin 2))).mapDerivedCategory).obj K0 ≅
      ((fInv (SimplexCategory.δ (0 : Fin 2))).mapDerivedCategory).obj K0) :
    cocycleRight J fInv compIso α =
      facePullback J fInv compIso 2 α ≫
        (eqToIso (congrArg (fun t ↦ (fInv t).mapDerivedCategory) (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2))
              (Fin.zero_le _)))).hom.app K0 ≫
        facePullback J fInv compIso 0 α ≫
        (eqToIso (congrArg (fun t ↦ (fInv t).mapDerivedCategory) (SimplexCategory.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2))
              le_rfl).symm)).hom.app K0 :=
  rfl

/-- The stage object `K_n = f_{τ^n_n}⁻¹ K_0`. -/
def ofCocycleObj (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (n : SimplexCategory) :
    DerivedCategory (Sheaf (J n) AddCommGrpCat.{w}) :=
  ((fInv (Sheaf.vertexOp n)).mapDerivedCategory).obj K0

/-- `ofCocycleObj K0 n` is the vertex pullback `f_{τ^n_n}⁻¹ K_0`. -/
theorem ofCocycleObj_eq (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (n : SimplexCategory) :
    ofCocycleObj J fInv K0 n =
      ((fInv (Sheaf.vertexOp n)).mapDerivedCategory).obj K0 :=
  rfl

/-- The edge-pullback transition isomorphism `K_φ : f_φ⁻¹ K_m ≅ K_n`, obtained by recoding along
`τ^m_m ≫ φ = τ^n_{φ(m)n}` and applying `(f_{τ^n_{φ(m)n}})⁻¹ α`. -/
def ofCocycleTransitionIso (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : ((fInv (SimplexCategory.δ (1 : Fin 2))).mapDerivedCategory).obj K0 ≅
      ((fInv (SimplexCategory.δ (0 : Fin 2))).mapDerivedCategory).obj K0)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    ((fInv φ).mapDerivedCategory).obj (ofCocycleObj J fInv K0 m) ≅
      ofCocycleObj J fInv K0 n :=
  (derivedInverseImageCompIso J fInv (Sheaf.vertexOp m) φ
      (compIso (Sheaf.vertexOp m) φ)).symm.app K0 ≪≫
    (eqToIso (congrArg (fun t ↦ (fInv t).mapDerivedCategory) (SimplexCategory.Hom.ext_zero_left (Sheaf.vertexOp m ≫ φ)
        (SimplexCategory.δ (1 : Fin 2) ≫ Sheaf.edgeOp φ)))).app K0 ≪≫
    (derivedInverseImageCompIso J fInv
      (SimplexCategory.δ (1 : Fin 2)) (Sheaf.edgeOp φ)
      (compIso (SimplexCategory.δ (1 : Fin 2))
        (Sheaf.edgeOp φ))).app K0 ≪≫
    ((fInv (Sheaf.edgeOp φ)).mapDerivedCategory).mapIso α ≪≫
    (derivedInverseImageCompIso J fInv
      (SimplexCategory.δ (0 : Fin 2)) (Sheaf.edgeOp φ)
      (compIso (SimplexCategory.δ (0 : Fin 2))
        (Sheaf.edgeOp φ))).symm.app K0 ≪≫
    (eqToIso (congrArg (fun t ↦ (fInv t).mapDerivedCategory) (SimplexCategory.Hom.ext_zero_left
        (SimplexCategory.δ (0 : Fin 2) ≫ Sheaf.edgeOp φ)
        (Sheaf.vertexOp n)))).app K0

/-- The forward map of `ofCocycleTransitionIso` is the edge-pullback formula for `K_φ`. -/
theorem ofCocycleTransitionIso_hom
    (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : ((fInv (SimplexCategory.δ (1 : Fin 2))).mapDerivedCategory).obj K0 ≅
      ((fInv (SimplexCategory.δ (0 : Fin 2))).mapDerivedCategory).obj K0)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (ofCocycleTransitionIso J fInv compIso K0 α φ).hom =
      ((derivedInverseImageCompIso J fInv (Sheaf.vertexOp m) φ
          (compIso (Sheaf.vertexOp m) φ)).symm.app K0 ≪≫
        (eqToIso (congrArg (fun t ↦ (fInv t).mapDerivedCategory) (SimplexCategory.Hom.ext_zero_left (Sheaf.vertexOp m ≫ φ)
            (SimplexCategory.δ (1 : Fin 2) ≫ Sheaf.edgeOp φ)))).app K0 ≪≫
        (derivedInverseImageCompIso J fInv
          (SimplexCategory.δ (1 : Fin 2)) (Sheaf.edgeOp φ)
          (compIso (SimplexCategory.δ (1 : Fin 2))
            (Sheaf.edgeOp φ))).app K0 ≪≫
        ((fInv (Sheaf.edgeOp φ)).mapDerivedCategory).mapIso α ≪≫
        (derivedInverseImageCompIso J fInv
          (SimplexCategory.δ (0 : Fin 2)) (Sheaf.edgeOp φ)
          (compIso (SimplexCategory.δ (0 : Fin 2))
            (Sheaf.edgeOp φ))).symm.app K0 ≪≫
        (eqToIso (congrArg (fun t ↦ (fInv t).mapDerivedCategory) (SimplexCategory.Hom.ext_zero_left
            (SimplexCategory.δ (0 : Fin 2) ≫ Sheaf.edgeOp φ)
            (Sheaf.vertexOp n)))).app K0).hom :=
  rfl

/-- The edge-pullback transitions satisfy composition whenever the comparison
family is associative and the coface isomorphism satisfies the degree-two cocycle. -/
theorem ofCocycle_map_comp (hassoc : IsAssociative J fInv compIso)
    (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : (fInv (SimplexCategory.δ (1 : Fin 2))).mapDerivedCategory.obj K0 ≅
      (fInv (SimplexCategory.δ (0 : Fin 2))).mapDerivedCategory.obj K0)
    (h : cocycleLeft J fInv compIso α = cocycleRight J fInv compIso α)
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (ofCocycleTransitionIso J fInv compIso K0 α (ψ ≫ φ)).hom =
      (derivedInverseImageCompIso J fInv ψ φ (compIso ψ φ)).hom.app
          (ofCocycleObj J fInv K0 l) ≫
        (fInv φ).mapDerivedCategory.map
          (ofCocycleTransitionIso J fInv compIso K0 α ψ).hom ≫
        (ofCocycleTransitionIso J fInv compIso K0 α φ).hom := sorry

/-- A degree-zero derived abelian sheaf and a coface cocycle determine a simplicial
system whose objects are the last-vertex inverse images and whose transitions are
edge-pullbacks of the coface isomorphism. -/
def ofCocycle [IsInverseImageContext J fInv compIso]
    (hassoc : IsAssociative J fInv compIso)
    (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : (fInv (SimplexCategory.δ (1 : Fin 2))).mapDerivedCategory.obj K0 ≅
      (fInv (SimplexCategory.δ (0 : Fin 2))).mapDerivedCategory.obj K0)
    (h : cocycleLeft J fInv compIso α = cocycleRight J fInv compIso α) :
    DerivedSystem J fInv compIso :=
  DerivedSystem.of inferInstance (ofCocycleObj J fInv K0)
    (fun φ ↦ (ofCocycleTransitionIso J fInv compIso K0 α φ).hom)
    (ofCocycle_map_comp J fInv compIso hassoc K0 α h)

/-- The object of the cocycle system in each degree is its last-vertex inverse image. -/
theorem ofCocycle_obj [IsInverseImageContext J fInv compIso]
    (hassoc : IsAssociative J fInv compIso)
    (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : (fInv (SimplexCategory.δ (1 : Fin 2))).mapDerivedCategory.obj K0 ≅
      (fInv (SimplexCategory.δ (0 : Fin 2))).mapDerivedCategory.obj K0)
    (h : cocycleLeft J fInv compIso α = cocycleRight J fInv compIso α)
    (n : SimplexCategory) :
    (ofCocycle J fInv compIso hassoc K0 α h).obj n = ofCocycleObj J fInv K0 n := rfl

/-- The transition of the cocycle system is the explicitly constructed edge-pullback map. -/
theorem ofCocycle_map [IsInverseImageContext J fInv compIso]
    (hassoc : IsAssociative J fInv compIso)
    (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : (fInv (SimplexCategory.δ (1 : Fin 2))).mapDerivedCategory.obj K0 ≅
      (fInv (SimplexCategory.δ (0 : Fin 2))).mapDerivedCategory.obj K0)
    (h : cocycleLeft J fInv compIso α = cocycleRight J fInv compIso α)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (ofCocycle J fInv compIso hassoc K0 α h).map φ =
      (ofCocycleTransitionIso J fInv compIso K0 α φ).hom := rfl

/-- The system associated to a coface cocycle is cartesian, since every transition
is the forward map of its edge-pullback isomorphism. -/
theorem ofCocycle_isCartesian [IsInverseImageContext J fInv compIso]
    (hassoc : IsAssociative J fInv compIso)
    (K0 : DerivedCategory (Sheaf (J ⦋0⦌) AddCommGrpCat.{w}))
    (α : (fInv (SimplexCategory.δ (1 : Fin 2))).mapDerivedCategory.obj K0 ≅
      (fInv (SimplexCategory.δ (0 : Fin 2))).mapDerivedCategory.obj K0)
    (h : cocycleLeft J fInv compIso α = cocycleRight J fInv compIso α) :
    IsCartesian (ofCocycle J fInv compIso hassoc K0 α h) := by
  intro m n φ
  change IsIso (ofCocycleTransitionIso J fInv compIso K0 α φ).hom
  infer_instance

end DerivedSystem

end CategoryTheory.SimplicialSites
