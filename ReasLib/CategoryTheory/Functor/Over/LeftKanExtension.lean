module

public import ReasLib.CategoryTheory.Limits.FiniteConnected.Preserves
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits

universe u v w

noncomputable section

namespace CategoryTheory.Over.Forget.LeftKanExtension

variable {C : Type u} [Category.{v} C]

namespace Index

/-- The discrete family of terminal objects used to calculate the left Kan extension along
`(Over.forget U).op` at `V`. -/
abbrev functor (U V : C) :
    Discrete (V ⟶ U) ⥤ CostructuredArrow (Over.forget U).op (op V) :=
  Discrete.functor fun φ ↦
    CostructuredArrow.mk
      (𝟙 ((Over.forget U).op.obj (op (Over.mk φ))))

/-- The discrete family of arrows `V ⟶ U` is final in the Kan-extension indexing category. -/
@[instance]
theorem final (U V : C) : Functor.Final (functor U V) := sorry

/-- The restriction of the Kan-extension indexing diagram to `Index.functor U V` is the discrete
family of values of `G` on maps `V ⟶ U`. -/
abbrev projIso
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) (V : C) :
    functor U V ⋙ CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G ≅
      Discrete.functor (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))) :=
  Discrete.natIso fun _ ↦ Iso.refl _

end Index

/-- The left Kan extension along `(Over.forget U).op` is objectwise the
coproduct of the values of `G` over maps `V ⟶ U`. -/
@[stacks 0494]
noncomputable def objIsoSigma
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) (V : C) :
    ((Over.forget U).op.lan.obj G).obj (op V) ≅
      Σ φ : V ⟶ U, G.obj (op (Over.mk φ)) :=
  (Over.forget U).op.leftKanExtensionObjIsoColimit G (op V) ≪≫
    (Functor.Final.colimitIso
      (Index.functor U V)
      (CostructuredArrow.proj (Over.forget U).op (op V) ⋙ G)).symm ≪≫
    HasColimit.isoOfNatIso (Index.projIso U G V) ≪≫
    Types.coproductIso.{v, max u w} (fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ)))

/-- The fiber of the left-Kan-extension sigma chart over a specified map is the corresponding
value of `G` in the slice category. -/
noncomputable def fiberIsoMk
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) {V : C} (φ : V ⟶ U) :
    {s : ((Over.forget U).op.lan.obj G).obj (op V) //
      ((objIsoSigma U G V).hom s).1 = φ} ≅
      G.obj (op (Over.mk φ)) :=
  ((Equiv.subtypeEquiv (objIsoSigma U G V).toEquiv (fun _ ↦ Iff.rfl)).trans
    (Equiv.sigmaSubtype φ)).toIso

/-- The fiber of the left-Kan-extension sigma chart over `X.hom` is canonically the value of `G`
at `X`. -/
noncomputable def fiberIso
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) (X : Over U) :
    {s : ((Over.forget U).op.lan.obj G).obj (op X.left) //
      ((objIsoSigma U G X.left).hom s).1 = X.hom} ≅
      G.obj (op X) :=
  fiberIsoMk U G X.hom

/-- The fiber equivalence reads the second coordinate of the sigma chart, up to the dependent
type transport forced by the first-coordinate equality. -/
theorem fiberIso.hom_heq_snd
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) (X : Over U)
    (s : ((Over.forget U).op.lan.obj G).obj (op X.left))
    (hs : ((objIsoSigma U G X.left).hom s).1 = X.hom) :
    HEq ((fiberIso U G X).hom ⟨s, hs⟩)
      ((objIsoSigma U G X.left).hom s).2 := sorry

/-- The sigma formula sends the unit generator associated to `a : V ⟶ U` to the corresponding
coproduct summand. -/
theorem objIsoSigma.hom_unitApp
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) {V : C}
    (a : V ⟶ U) (s : G.obj (op (Over.mk a))) :
    (objIsoSigma U G V).hom
        (((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a)) s) =
      ⟨a, s⟩ := sorry

/-- The inverse sigma chart sends a summand element to the corresponding left-Kan-extension
unit generator. -/
@[simp]
theorem objIsoSigma.inv_mk
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) {V : C}
    (a : V ⟶ U) (s : G.obj (op (Over.mk a))) :
    (objIsoSigma U G V).inv ⟨a, s⟩ =
      (((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s := sorry

/-- The inverse fiber chart has the expected underlying left-Kan-extension unit generator. -/
@[simp]
theorem fiberIsoMk.inv_val
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w)) {V : C}
    (a : V ⟶ U) (s : G.obj (op (Over.mk a))) :
    ((fiberIsoMk U G a).inv s).1 =
      (((Over.forget U).op.leftKanExtensionUnit G).app (op (Over.mk a))) s := sorry

/-- The inverse fiber chart at a slice object has the expected underlying unit generator. -/
@[simp]
theorem fiberIso.inv_val
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w))
    (X : Over U) (s : G.obj (op X)) :
    ((fiberIso U G X).inv s).1 =
      (((Over.forget U).op.leftKanExtensionUnit G).app (op X)) s := sorry

/-- In sigma coordinates, restriction along `f : Y ⟶ V` postcomposes the index and restricts its
section along the induced map in `Over U`. -/
theorem objIsoSigma.hom_map
    (U : C) (G : (Over U)ᵒᵖ ⥤ Type (max u v w))
    {V Y : C} (f : Y ⟶ V) (x : ((Over.forget U).op.lan.obj G).obj (op V)) :
    (objIsoSigma U G Y).hom (((Over.forget U).op.lan.obj G).map f.op x) =
      ⟨f ≫ ((objIsoSigma U G V).hom x).1,
        G.map
          (Over.homMk f :
            Over.mk (f ≫ ((objIsoSigma U G V).hom x).1) ⟶
              Over.mk ((objIsoSigma U G V).hom x).1).op
          ((objIsoSigma U G V).hom x).2⟩ := sorry

/-- Left Kan extension along `(Over.forget U).op` preserves limits of
finite connected diagrams of type-valued presheaves. -/
@[stacks 0494, instance]
theorem preservesFiniteConnectedLimits (U : C) :
    PreservesFiniteConnectedLimits
      ((Over.forget U).op.lan :
        ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) := sorry

/-- The presheaf-level localization lower shriek preserves pullbacks. -/
@[stacks 0494]
theorem preservesPullbacks (U : C) :
    PreservesLimitsOfShape WalkingCospan
      ((Over.forget U).op.lan :
        ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) := sorry

/-- The presheaf-level localization lower shriek preserves equalizers. -/
@[stacks 0494]
theorem preservesEqualizers (U : C) :
    PreservesLimitsOfShape WalkingParallelPair
      ((Over.forget U).op.lan :
        ((Over U)ᵒᵖ ⥤ Type (max u v)) ⥤ (Cᵒᵖ ⥤ Type (max u v))) := sorry

end CategoryTheory.Over.Forget.LeftKanExtension
