module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.CategoryTheory.Fibered.Groupoids.SliceBaseChange
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.CategoryTheory.Presheaf.Basic

/-!
# Computing presheaf pushforward on a fibre object

The source identification `f_* F(y) ≅ Γ((Sch/V)_fppf ×_{y, Y} X, pr⁻¹ F)` as a
Type-valued isomorphism between pointwise right Kan extension evaluation and the
limit of the pulled-back presheaf on the Yoneda 2-fibre product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits Opposite FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u w

namespace CategoryTheory.FiberedCategoryOver.Groupoids

variable {S : Scheme.{u}}
variable {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}

/-- The 2-fibre product `(Sch/V)_fppf ×_{y, Y} X` of the 2-Yoneda representative of
`y` with a 1-morphism `f : X ⟶ Y`. -/
noncomputable abbrev yonedaFibreProduct (f : X ⟶ Y) {V : Over S} (y : Y.p.Fiber V) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S) :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} (YonedaSlice.representative y) f

/-- The 2-fibre product `(Sch/V)_fppf ×_{y, Y} X` is the explicit apex of the
Yoneda representative of `y` with `f`. -/
@[simp]
theorem yonedaFibreProduct_apex (f : X ⟶ Y) {V : Over S} (y : Y.p.Fiber V) :
    yonedaFibreProduct f y =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} (YonedaSlice.representative y) f :=
  sorry

namespace yonedaFibreProduct

/-- The projection `pr : (Sch/V)_fppf ×_{y, Y} X ⟶ X`. -/
noncomputable abbrev pr (f : X ⟶ Y) {V : Over S} (y : Y.p.Fiber V) :
    yonedaFibreProduct f y ⟶ X :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} (YonedaSlice.representative y) f

/-- The projection `pr` is the second projection of the Yoneda 2-fibre product. -/
@[simp]
theorem pr_snd (f : X ⟶ Y) {V : Over S} (y : Y.p.Fiber V) :
    pr f y = TwoFibreProduct.snd.{u + 1, u, u + 1, u} (YonedaSlice.representative y) f :=
  sorry

/-- The morphism `f(pr(q)) ⟶ y` encoded by an object of the Yoneda 2-fibre product. -/
noncomputable def arrow (f : X ⟶ Y) {V : Over S} (y : Y.p.Fiber V)
    (q : (yonedaFibreProduct f y).total) :
    (toFunctor f).obj ((toFunctor (pr f y)).obj q) ⟶ y.1 :=
  (toNatTrans
        (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u}
          (YonedaSlice.representative y) f).inv).app q ≫
    (toFunctor (YonedaSlice.representative y)).map
      (Over.mkIdTerminal.from
        ((toFunctor
            (TwoFibreProduct.fst.{u + 1, u, u + 1, u}
              (YonedaSlice.representative y) f)).obj q)) ≫
    (YonedaSlice.representative.fiberObjIso y).hom.1

/-- The functor sending an object of the Yoneda 2-fibre product to the corresponding
structured arrow `f(pr(q)) ⟶ y`. -/
noncomputable def toStructuredArrow (f : X ⟶ Y) {V : Over S} (y : Y.p.Fiber V) :
    (yonedaFibreProduct f y).totalᵒᵖ ⥤ StructuredArrow (op y.1) (toFunctor f).op where
  obj q := StructuredArrow.mk (op (arrow f y q.unop))
  map {q q'} ψ :=
    StructuredArrow.homMk ((toFunctor (pr f y)).op.map ψ) sorry
  map_id := sorry
  map_comp := sorry

end yonedaFibreProduct

variable (f : X ⟶ Y)
variable [∀ P : Presheaf X.total, (toFunctor f).op.HasRightKanExtension P]

/-- Reindexing the pulled-back presheaf along `toStructuredArrow` does not change the
existence of its limit. -/
instance yonedaFibreProduct.hasLimit_toStructuredArrow_comp {V : Over S}
    (y : Y.p.Fiber V) (F : Presheaf X.total)
    [HasLimit ((toFunctor (yonedaFibreProduct.pr f y)).op ⋙ F)] :
    HasLimit
      (yonedaFibreProduct.toStructuredArrow f y ⋙
        StructuredArrow.proj (op y.1) (toFunctor f).op ⋙ F) :=
  hasLimit_of_iso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry :
      ((toFunctor (yonedaFibreProduct.pr f y)).op ⋙ F) ≅
        yonedaFibreProduct.toStructuredArrow f y ⋙
          StructuredArrow.proj (op y.1) (toFunctor f).op ⋙ F)

/-- The forward map of the identification `f_* F(y) ⟶ Γ((Sch/V)_fppf ×_{y, Y} X, pr⁻¹ F)`,
obtained by evaluating the pointwise right Kan extension as a comma limit and reindexing
along `yonedaFibreProduct.toStructuredArrow`. -/
noncomputable def pushforwardObjIsoGlobalSectionsHom {V : Over S} (y : Y.p.Fiber V)
    (F : Presheaf X.total)
    [(toFunctor f).op.HasPointwiseRightKanExtension F]
    [HasLimit ((toFunctor (yonedaFibreProduct.pr f y)).op ⋙ F)] :
    ((toFunctor f).op.ran.obj F).obj (op y.1) ⟶
      limit ((toFunctor (yonedaFibreProduct.pr f y)).op ⋙ F) :=
  ((toFunctor f).op.ranObjObjIsoLimit F (op y.1)).hom ≫
    limit.pre (StructuredArrow.proj (op y.1) (toFunctor f).op ⋙ F)
      (yonedaFibreProduct.toStructuredArrow f y)

/-- The forward map of `pushforwardObjIsoGlobalSections` is an isomorphism, because the
Yoneda 2-fibre product is equivalent to the comma category of arrows `f(x) ⟶ y`. -/
instance pushforwardObjIsoGlobalSections.isIso {V : Over S} (y : Y.p.Fiber V)
    (F : Presheaf X.total)
    [(toFunctor f).op.HasPointwiseRightKanExtension F]
    [HasLimit ((toFunctor (yonedaFibreProduct.pr f y)).op ⋙ F)] :
    IsIso (pushforwardObjIsoGlobalSectionsHom f y F) :=
  sorry

/-- 96.5.0.1: for a 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over
`(Sch/S)_fppf`, a presheaf `F` on `X`, and an object `y` of `Y` over a scheme `V`,
there is a canonical identification
`((toFunctor f).op.ran.obj F).obj (op y.1) ≅
  limit ((toFunctor (yonedaFibreProduct.pr f y)).op ⋙ F)`,
i.e. `f_* F(y) ≅ Γ((Sch/V)_fppf ×_{y, Y} X, pr⁻¹ F)`, where `y` is viewed by
2-Yoneda as `YonedaSlice.representative y : slice V ⟶ Y` and `pr` is the
projection of that 2-fibre product to `X`. Pushforward is the chosen right Kan
extension along `(toFunctor f).op`, `pr⁻¹` is precomposition with
`(toFunctor pr).op`, and `Γ` of a Type-valued presheaf is the limit. -/
@[stacks 06W6]
noncomputable def pushforwardObjIsoGlobalSections {V : Over S} (y : Y.p.Fiber V)
    (F : Presheaf X.total)
    [(toFunctor f).op.HasPointwiseRightKanExtension F]
    [HasLimit ((toFunctor (yonedaFibreProduct.pr f y)).op ⋙ F)] :
    ((toFunctor f).op.ran.obj F).obj (op y.1) ≅
      limit ((toFunctor (yonedaFibreProduct.pr f y)).op ⋙ F) :=
  asIso (pushforwardObjIsoGlobalSectionsHom f y F)

/-- The identification `f_* F(y) ≅ Γ((Sch/V)_fppf ×_{y, Y} X, pr⁻¹ F)` computes on
an object `q` of the Yoneda 2-fibre product as the limit projection of `pr⁻¹ F`
at `pr(q)`, equivalently the right Kan extension counit on the corresponding
structured arrow. -/
theorem pushforwardObjIsoGlobalSections_π {V : Over S} (y : Y.p.Fiber V)
    (F : Presheaf X.total)
    [(toFunctor f).op.HasPointwiseRightKanExtension F]
    [HasLimit ((toFunctor (yonedaFibreProduct.pr f y)).op ⋙ F)]
    (q : (yonedaFibreProduct f y).total) :
    (pushforwardObjIsoGlobalSections f y F).hom ≫
        limit.π ((toFunctor (yonedaFibreProduct.pr f y)).op ⋙ F) (op q) =
      ((toFunctor f).op.ran.obj F).map (op (yonedaFibreProduct.arrow f y q)) ≫
        ((toFunctor f).op.ranCounit.app F).app
          (op ((toFunctor (yonedaFibreProduct.pr f y)).obj q)) :=
  sorry

/-- The identification `f_* F(y) ≅ Γ((Sch/V)_fppf ×_{y, Y} X, pr⁻¹ F)` is natural
in the presheaf `F`. -/
theorem pushforwardObjIsoGlobalSections_natural {V : Over S} (y : Y.p.Fiber V)
    {F G : Presheaf X.total} (τ : F ⟶ G)
    [(toFunctor f).op.HasPointwiseRightKanExtension F]
    [(toFunctor f).op.HasPointwiseRightKanExtension G]
    [HasLimit ((toFunctor (yonedaFibreProduct.pr f y)).op ⋙ F)]
    [HasLimit ((toFunctor (yonedaFibreProduct.pr f y)).op ⋙ G)] :
    (pushforwardObjIsoGlobalSections f y F).hom ≫
        limMap (whiskerLeft (toFunctor (yonedaFibreProduct.pr f y)).op τ) =
      ((toFunctor f).op.ran.map τ).app (op y.1) ≫
        (pushforwardObjIsoGlobalSections f y G).hom :=
  sorry

end CategoryTheory.FiberedCategoryOver.Groupoids
