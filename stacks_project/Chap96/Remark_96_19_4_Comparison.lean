module

public import Mathlib.Algebra.Homology.Functor
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.«96_5_0_1»
public import stacks_project.Chap96.Lemma_96_18_1_Cech
public import stacks_project.Chap96.Lemma_96_18_1_Comparison
public import stacks_project.Chap96.Lemma_96_19_2_RelativeCech

/-!
# Evaluation of the relative Čech complex on a fibre object

The canonical identification of `Γ(x, K^•(f, F))` with the ordinary Čech complex
of the Yoneda base change of `f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicTopology Functor Limits Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- The base change `g : V ⟶ Y` of a 1-morphism `f : U ⟶ X` along the 2-Yoneda
representative of a fibre object `x` of `X` over `W`. Here `Y` is
`GroupoidsOver.slice W` and `V` is `yonedaFibreProduct f x`. -/
def yonedaBaseChange (f : U ⟶ X) {W : Over S} (x : X.p.Fiber W) :
    yonedaFibreProduct f x ⟶ GroupoidsOver.slice W :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u} (YonedaSlice.representative x) f

/-- The covering-simplex functor `V_n ⥤ U_n` induced by the 2-cartesian square
of the Yoneda fibre product of `f` with `x`. -/
def sectionsCoveringMap (f : U ⟶ X) {W : Over S} (x : X.p.Fiber W)
    (n : SimplexCategory) :
    Cech.Simplex.Obj (yonedaBaseChange f x) n ⥤ Cech.Simplex.Obj f n :=
  Cech.coveringMapFunctor
    (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u}
      (YonedaSlice.representative x) f).symm n

/-- The morphism from the apex of the covering-simplex image in `U_n` to the
fibre object `x.1`, obtained by evaluating the 2-Yoneda representative on the
identity of `W`. -/
def sectionsArrow (f : U ⟶ X) {W : Over S} (x : X.p.Fiber W)
    (n : SimplexCategory) (P : Cech.Simplex.Obj (yonedaBaseChange f x) n) :
    (Cech.apexFunctor f n).obj ((sectionsCoveringMap f x n).obj P) ⟶ x.1 :=
  (toFunctor (YonedaSlice.representative x)).map (Over.mkIdTerminal.from P.apex) ≫
    (YonedaSlice.representative.fiberObjIso x).hom.1

/-- Reindexing functor from covering simplices of the Yoneda base change to the
comma category of the apex functor of `f` over `x`. -/
def sectionsToStructuredArrow (f : U ⟶ X) {W : Over S} (x : X.p.Fiber W)
    (n : SimplexCategory) :
    (Cech.Simplex.Obj (yonedaBaseChange f x) n)ᵒᵖ ⥤
      StructuredArrow (op x.1) (Cech.apexFunctor f n).op where
  obj q :=
    StructuredArrow.mk
      ((sectionsArrow f x n q.unop).op :
        op x.1 ⟶
          (Cech.apexFunctor f n).op.obj (op ((sectionsCoveringMap f x n).obj q.unop)))
  map {q q'} ψ := StructuredArrow.homMk ((sectionsCoveringMap f x n).op.map ψ) sorry
  map_id := sorry
  map_comp := sorry

/-- The covering-simplex map `V_n ⟶ U_n` of Lemma 96.18.1 induces an equivalence
from covering simplices of the Yoneda base change to the 96.5.0.1 comma
category of `U_n` over `x`, hence `V_n ≃ (Sch/W)_fppf ×_{x, X} U_n`. -/
theorem coveringSimplex_isEquivalence (f : U ⟶ X) {W : Over S} (x : X.p.Fiber W)
    (n : SimplexCategory) :
    Functor.IsEquivalence (sectionsToStructuredArrow f x n) :=
  sorry

variable (f : U ⟶ X) {W : Over S} (x : X.p.Fiber W)
variable (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1})
variable [∀ (n : SimplexCategory) (G : (Cech.Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
    HasRightKanExtension (Cech.apexFunctor f n).op G]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n)
    (G : (Cech.Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
    HasRightKanExtension (Cech.reindex φ).op G]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n)
    (G : (Cech.Simplex.Obj f n)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
    HasRightKanExtension ((Cech.reindex φ).op ⋙ (Cech.apexFunctor f m).op) G]
variable [∀ n : ℕ,
    (Cech.apexFunctor f ⦋n⦌).op.HasPointwiseRightKanExtension
      ((Cech.apexFunctor f ⦋n⦌).op ⋙ F)]
variable [∀ n : ℕ,
    HasLimit (StructuredArrow.proj (op x.1) (Cech.apexFunctor f ⦋n⦌).op ⋙
      (Cech.apexFunctor f ⦋n⦌).op ⋙ F)]

/-- Degree-`n` forward map of the identification of the relative Čech complex at
`x` with ordinary Čech of the Yoneda base change. -/
def sectionsHom_f (n : ℕ) :
    ((complex f F).asFunctor.obj (op x.1)).X n ⟶
      (Cech.complex (yonedaBaseChange f x)
          (Cech.inverseImage (YonedaSlice.representative x) F)).X n :=
  AddCommGrpCat.ofHom
    { toFun := fun a ↦
        ⟨fun q ↦
          (forget AddCommGrpCat.{u + 1}).map
            (((Cech.apexFunctor f ⦋n⦌).op.ranObjObjIsoLimit
                  ((Cech.apexFunctor f ⦋n⦌).op ⋙ F) (op x.1)).hom ≫
              limit.π
                (StructuredArrow.proj (op x.1) (Cech.apexFunctor f ⦋n⦌).op ⋙
                  (Cech.apexFunctor f ⦋n⦌).op ⋙ F)
                ((sectionsToStructuredArrow f x ⦋n⦌).obj q))
            a,
          sorry⟩
      map_zero' := sorry
      map_add' := sorry }

/-- The forward morphism of complexes from the evaluated relative Čech complex to `Cech.complex` of the Yoneda base change. -/
def sectionsHom :
    (complex f F).asFunctor.obj (op x.1) ⟶
      Cech.complex (yonedaBaseChange f x)
        (Cech.inverseImage (YonedaSlice.representative x) F) where
  f n := sectionsHom_f f x F n
  comm' := sorry

/-- The forward map of `sectionsIso` is an isomorphism, because the covering
simplices of the Yoneda base change are equivalent to the comma category of
`U_n` over `x`. -/
instance sectionsHom.isIso : IsIso (sectionsHom f x F) :=
  sorry

/-- Identification of the relative Čech complex of `f` evaluated at a fibre
object `x` with the ordinary Čech complex of the Yoneda base change of `f`. -/
def sectionsIso :
    (complex f F).asFunctor.obj (op x.1) ≅
      Cech.complex (yonedaBaseChange f x)
        (Cech.inverseImage (YonedaSlice.representative x) F) :=
  asIso (sectionsHom f x F)

/-- Degree `n` of `sectionsIso` as an isomorphism of abelian groups. -/
def sectionsIso_X (n : ℕ) :
    ((complex f F).asFunctor.obj (op x.1)).X n ≅
      (Cech.complex (yonedaBaseChange f x)
          (Cech.inverseImage (YonedaSlice.representative x) F)).X n :=
  HomologicalComplex.Hom.isoApp (sectionsIso f x F) n

/-- Degree `n` of `sectionsIso` is `sectionsHom_f`. -/
theorem sectionsIso_hom_f (n : ℕ) :
    (sectionsIso f x F).hom.f n = sectionsHom_f f x F n :=
  sorry

/-- The underlying morphism of `sectionsIso_X` is `sectionsHom_f`. -/
theorem sectionsIso_X_hom (n : ℕ) :
    (sectionsIso_X f x F n).hom = sectionsHom_f f x F n :=
  sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech
