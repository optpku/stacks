module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Cech.Comparison
public import ReasLib.CategoryTheory.Fibered.Groupoids.RelativeCech.Complex
public import ReasLib.CategoryTheory.Fibered.Groupoids.SliceBaseChange
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids

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
representative of a fibre object `x` of `X` over `W`, with target the canonical
slice groupoid over `W`. -/
def yonedaBaseChange (f : U ⟶ X) {W : Over S} (x : X.p.Fiber W) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} (YonedaSlice.representative x) f ⟶
      GroupoidsOver.slice W :=
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

/-- Covering simplices of the Yoneda base change are equivalent to the comma
category of the apex functor over the given fibre object. -/
instance coveringSimplex_isEquivalence (f : U ⟶ X) {W : Over S} (x : X.p.Fiber W)
    (n : SimplexCategory) :
    Functor.IsEquivalence (sectionsToStructuredArrow f x n) :=
  sorry

variable (f : U ⟶ X) {W : Over S} (x : X.p.Fiber W)
variable (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{u + 1})

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

/-- The canonical comparison from the evaluated relative Čech complex to the
Čech complex of the Yoneda base change is invertible. -/
instance sectionsHom.isIso : IsIso (sectionsHom f x F) :=
  sorry

/-- Each degree of the canonical sections comparison is invertible. -/
instance sectionsHom_f.isIso (n : ℕ) : IsIso (sectionsHom_f f x F n) :=
  inferInstanceAs (IsIso ((sectionsHom f x F).f n))

/-- The degree-`n` component of the sections comparison is its explicit
degreewise limit-projection map. -/
theorem sectionsHom_f_eq (n : ℕ) :
    (sectionsHom f x F).f n = sectionsHom_f f x F n :=
  rfl

end CategoryTheory.FiberedCategoryOver.Groupoids.RelativeCech
