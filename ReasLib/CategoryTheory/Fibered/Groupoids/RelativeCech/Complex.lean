module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import ReasLib.CategoryTheory.Sites.Presheaf.Pullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Cech.Simplex

/-!
# The relative Čech complex of a 1-morphism of categories fibred in groupoids

The complex `K^•(f, F)` of abelian presheaves on `X` with terms
`f_{n,*} f_n⁻¹ F`, obtained from covering simplices by right Kan extension
along the apex functors and the alternating coface construction on the resulting
cosimplicial object.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology Functor
open scoped Bicategory Simplicial

noncomputable section

universe u v w vS wA

namespace CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech

open Cech

variable {C : Type u} [Category.{v} C]
variable {U X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

/-- The `n`-th term of the relative Čech complex: `f_{n,*} f_n⁻¹ F`. -/
def term (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : SimplexCategory)
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f n).op G] :
    X.totalᵒᵖ ⥤ AddCommGrpCat.{wA} :=
  (apexFunctor f n).op.ran.obj ((apexFunctor f n).op ⋙ F)

/-- Degree `n` of the relative Čech complex is `f_{n,*} f_n⁻¹ F`. -/
theorem term_eq (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : SimplexCategory)
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f n).op G] :
    term f F n = (apexFunctor f n).op.ran.obj ((apexFunctor f n).op ⋙ F) :=
  rfl

/-- Degreewise coface `f_{m,*} f_m⁻¹ F ⟶ f_{n,*} f_n⁻¹ F`. -/
def cofaceApp (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    {m n : SimplexCategory} (φ : m ⟶ n)
    [∀ G : (Simplex.Obj f m)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f m).op G]
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension (reindex φ).op G]
    [∀ G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA},
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] :
    term f F m ⟶ term f F n :=
  (presheafPullbackMap (reindex φ) (apexFunctor f m)
    (g := apexFunctor f n)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro P Q a
      change a.apex ≫ 𝟙 _ = 𝟙 _ ≫ a.apex
      simp))).app
      ((apexFunctor f m).op ⋙ F)

/-- The canonical coface map associated to an identity is the identity. -/
theorem cofaceApp_id (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] (n : SimplexCategory) :
    cofaceApp f F (𝟙 n) = 𝟙 (term f F n) :=
  sorry

/-- The canonical coface maps respect composition of simplex morphisms. -/
theorem cofaceApp_comp (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] {m n p : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ p) :
    cofaceApp f F (φ ≫ ψ) = cofaceApp f F φ ≫ cofaceApp f F ψ :=
  sorry

/-- The cosimplicial abelian presheaf `n ↦ f_{n,*} f_n⁻¹ F` on `X`. -/
def cosimplicial (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] :
    CosimplicialObject (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) where
  obj n := term f F n
  map φ := cofaceApp f F φ
  map_id := cofaceApp_id f F
  map_comp := cofaceApp_comp f F

/-- The relative Čech complex `K^•(f, F)` of abelian presheaves on `X`. -/
def complex (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA})
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] :
    CochainComplex (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) ℕ :=
  (alternatingCofaceMapComplex _).obj (cosimplicial f F)

/-- Degree `n` of `RelativeCech.complex` is `f_{n,*} f_n⁻¹ F`. -/
theorem complex_X (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ)
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] :
    (complex f F).X n = term f F ⦋n⦌ :=
  rfl

/-- The relative Čech differential is the alternating sum of coface maps. -/
theorem complex_d (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) (n : ℕ)
    [∀ (n : SimplexCategory) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (apexFunctor f n).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension (reindex φ).op G]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n) (G : (Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{wA}),
      HasRightKanExtension ((reindex φ).op ⋙ (apexFunctor f m).op) G] :
    (complex f F).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (cosimplicial f F).δ i :=
  sorry

variable {Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

/-- Inverse image of a complex of abelian presheaves along a 1-morphism. -/
def inverseImageComplex (e : Y ⟶ X) (K : CochainComplex (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) ℕ) :
    CochainComplex (Y.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) ℕ :=
  ((presheafInverseImage (toFunctor e) AddCommGrpCat.{wA}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K

/-- Degree `n` of `inverseImageComplex e K` is the inverse image of the degree-`n` term. -/
theorem inverseImageComplex_X (e : Y ⟶ X)
    (K : CochainComplex (X.totalᵒᵖ ⥤ AddCommGrpCat.{wA}) ℕ) (n : ℕ) :
    (inverseImageComplex e K).X n =
      (presheafInverseImage (toFunctor e) AddCommGrpCat.{wA}).obj (K.X n) :=
  rfl

end CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech
