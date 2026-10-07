module

public import Mathlib.Data.Fin.Tuple.Basic
public import ReasLib.Algebra.Homology.Homotopy.Contractible
public import ReasLib.AlgebraicTopology.CosimplicialObject.Augmented.AlternatingCoface
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Lemma_96_18_1_Cech

/-!
# The extended Čech complex of a 1-morphism of categories fibred in groupoids

The coaugmentation `Γ(X, F) ⟶ Γ(U_0, f_0⁻¹ F)`, the ℕ-indexed extended
complex obtained by placing that term in degree 0, and the extra
degeneracy on covering simplices induced by a section up to 2-isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicTopology
open scoped Bicategory Simplicial

noncomputable section

universe u v w vS wA

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Cech

variable {C : Type u} [Category.{v} C]
variable {U X : FiberedCategoryOver.Groupoids C}

/-- The last structure isomorphism of the extra-degeneracy covering simplex,
obtained by transporting the section 2-isomorphism along `toFunctor.comp` and
`toFunctor.id`. -/
def extraSimplexLastIso {f : U ⟶ X} (s : X ⟶ U) (t : s ≫ f ≅ 𝟙 X) (x : X.total) :
    (toFunctor f).obj ((toFunctor s).obj x) ≅ x :=
  eqToIso (Functor.congr_obj (toFunctor.comp s f).symm x) ≪≫
    (toFunctorIso t).app x ≪≫
    eqToIso (Functor.congr_obj (toFunctor.id X) x)

/-- Vertices of the extra-degeneracy covering simplex: the original vertices,
followed by `s` of the apex. -/
def extraSimplexVertices {f : U ⟶ X} (s : X ⟶ U) {n : SimplexCategory}
    (P : Simplex.Obj f n) : Fin (n.len + 2) → U.total :=
  Fin.snoc P.vertices ((toFunctor s).obj P.apex)

/-- The extra-degeneracy vertices restrict to the original vertices on
`Fin.castSucc`. -/
theorem extraSimplexVertices_castSucc {f : U ⟶ X} (s : X ⟶ U)
    {n : SimplexCategory} (P : Simplex.Obj f n) (i : Fin (n.len + 1)) :
    extraSimplexVertices s P i.castSucc = P.vertices i :=
  sorry

/-- The last extra-degeneracy vertex is `s` of the apex. -/
theorem extraSimplexVertices_last {f : U ⟶ X} (s : X ⟶ U)
    {n : SimplexCategory} (P : Simplex.Obj f n) :
    extraSimplexVertices s P (Fin.last (n.len + 1)) = (toFunctor s).obj P.apex :=
  sorry

/-- Structure isomorphisms of the extra-degeneracy covering simplex, appending
the transported section 2-isomorphism at the last vertex. -/
def extraSimplexIso {f : U ⟶ X} (s : X ⟶ U) (t : s ≫ f ≅ 𝟙 X)
    {n : SimplexCategory} (P : Simplex.Obj f n) :
    ∀ i : Fin (n.len + 2), (toFunctor f).obj (extraSimplexVertices s P i) ≅ P.apex :=
  fun i ↦
    Fin.lastCases
      (eqToIso (congrArg (fun u ↦ (toFunctor f).obj u) (extraSimplexVertices_last s P)) ≪≫
        extraSimplexLastIso s t P.apex)
      (fun j ↦
        eqToIso (congrArg (fun u ↦ (toFunctor f).obj u)
            (extraSimplexVertices_castSucc s P j)) ≪≫
          P.iso j)
      i

/-- Vertex maps of an extra-degeneracy covering-simplex morphism, appending the
image of the apex map under `s`. -/
def extraSimplexHomVertex {f : U ⟶ X} (s : X ⟶ U) {n : SimplexCategory}
    {P Q : Simplex.Obj f n} (ψ : Simplex.Hom P Q) :
    ∀ i : Fin (n.len + 2), extraSimplexVertices s P i ⟶ extraSimplexVertices s Q i :=
  fun i ↦
    Fin.lastCases
      (eqToHom (extraSimplexVertices_last s P) ≫
        (toFunctor s).map ψ.apex ≫
        eqToHom (extraSimplexVertices_last s Q).symm)
      (fun j ↦
        eqToHom (extraSimplexVertices_castSucc s P j) ≫
          ψ.vertex j ≫
          eqToHom (extraSimplexVertices_castSucc s Q j).symm)
      i

/-- The extra degeneracy `s_n : U_n ⥤ U_{n+1}` on covering simplices, sending
`(u_0, …, u_n, x, α_0, …, α_n)` to `(u_0, …, u_n, s(x), x, α_0, …, α_n, t_x)`. -/
def extraSimplexFunctor {f : U ⟶ X} (s : X ⟶ U) (t : s ≫ f ≅ 𝟙 X)
    (n : SimplexCategory) :
    Simplex.Obj f n ⥤ Simplex.Obj f (SimplexCategory.mk (n.len + 1)) where
  obj P := Simplex.objMk (extraSimplexVertices s P) P.apex (extraSimplexIso s t P)
  map ψ := Simplex.homMk (extraSimplexHomVertex s ψ) ψ.apex sorry
  map_id := sorry
  map_comp := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Cech

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Cech

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- The coaugmentation `Γ(X, F) ⟶ Γ(U_0, f_0⁻¹ F)` of the Čech complex, given by
pullback of global sections along `f_0`. -/
def coaugmentation (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    globalSections F ⟶ (complex f F).X 0 :=
  globalSectionsMap (apexFunctor f ⦋0⦌) F ≫ eqToHom (complex_X f F 0).symm

/-- The Čech coaugmentation equalizes every pair of maps out of `⦋0⦌`. -/
theorem coaugmentation_comp_map (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (i : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ i) :
    coaugmentation f F ≫ eqToHom (complex_X f F 0) ≫ (cosimplicial f F).map g₁ =
      coaugmentation f F ≫ eqToHom (complex_X f F 0) ≫ (cosimplicial f F).map g₂ :=
  sorry

/-- The augmented Čech cosimplicial abelian group of `f` and `F`, with
augmentation object `Γ(X, F)`. -/
def augmented (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    CosimplicialObject.Augmented AddCommGrpCat :=
  (cosimplicial f F).augment (globalSections F)
    (coaugmentation f F ≫ eqToHom (complex_X f F 0))
    (coaugmentation_comp_map f F)

/-- The coaugmentation is a cocycle in degree 0 of the ordinary Čech complex. -/
theorem coaugmentation_comp_d (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    coaugmentation f F ≫ (complex f F).d 0 1 = 0 :=
  sorry

/-- The extended Čech cochain complex of a 1-morphism of categories fibred in
groupoids and an abelian presheaf, obtained by placing `Γ(X, F)` in degree 0. -/
def extended (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    CochainComplex AddCommGrpCat ℕ :=
  CochainComplex.augment (complex f F) (coaugmentation f F) (coaugmentation_comp_d f F)

/-- Degree 0 of the extended Čech complex is `Γ(X, F)`, the source term in
degree -1. -/
theorem extended_X_zero (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (extended f F).X 0 = globalSections F :=
  sorry

/-- Positive degrees of the extended Čech complex recover the ordinary Čech
complex. -/
theorem extended_X_succ (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    (extended f F).X (n + 1) = (complex f F).X n :=
  sorry

/-- The first differential of the extended Čech complex is the coaugmentation. -/
theorem extended_d_zero_one (f : U ⟶ X) (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (extended f F).d 0 1 = coaugmentation f F :=
  sorry

/-- The extended Čech complex of an abelian presheaf is contractible whenever
the covering 1-morphism admits a section up to 2-isomorphism. -/
theorem extended_contractible_of_section (f : U ⟶ X) (s : X ⟶ U) (t : s ≫ f ≅ 𝟙 X)
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (extended f F).Contractible :=
  sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Cech
