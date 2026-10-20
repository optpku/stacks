module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Presheaf

/-!
# Graph comparison from étale extension by zero to finite-support lower shriek

The canonical presheaf map `j_{p!} ⟶ f_{p!}` along an étale morphism, induced
by sending a section on `W : U.Etale` to the finite-support term of its graph
in `U ×_X W`, then left Kan extending and sheafifying.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open FiniteSupport

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- The graph of `W.hom : W.left ⟶ U` as a morphism into the base change
`U ×_X W`. -/
def graphHom (W : U.Etale) :
    W.left ⟶ baseChangeScheme j ((etaleRestriction j).obj W) :=
  pullback.lift (𝟙 W.left) W.hom

/-- The first projection of the graph is the identity on `W`. -/
theorem graphHom_fst (W : U.Etale) :
    graphHom j W ≫ pullback.fst ((etaleRestriction j).obj W).hom j = 𝟙 W.left :=
  pullback.lift_fst _ _ _

/-- The second projection of the graph recovers `W.hom`. -/
theorem graphHom_snd (W : U.Etale) :
    graphHom j W ≫ pullback.snd ((etaleRestriction j).obj W).hom j = W.hom :=
  pullback.lift_snd _ _ _

/-- The graph of an étale `U`-scheme into `U ×_X W` is an open immersion. -/
instance graphHom_isOpenImmersion (W : U.Etale) :
    IsOpenImmersion (graphHom j W) :=
  sorry

/-- The composite of the graph with the projection to `W` is finite. -/
instance graphHom_toBase_isFinite (W : U.Etale) :
    IsFinite
      (graphHom j W ≫ baseChangeToBase j ((etaleRestriction j).obj W)) :=
  sorry

/-- The open-range inclusion of the graph, composed with the structure map to
`U`, is étale. -/
instance graphRange_hom_etale (W : U.Etale) :
    Etale
      ((graphHom j W).opensRange.ι ≫
        baseChangeToSource j ((etaleRestriction j).obj W)) :=
  sorry

/-- The open image of the graph, as an object of `U.Etale`. -/
def graphRangeObject (W : U.Etale) : U.Etale :=
  Scheme.Etale.mk
    ((graphHom j W).opensRange.ι ≫
      baseChangeToSource j ((etaleRestriction j).obj W))

/-- The canonical range isomorphism of the graph respects structure maps to
`U`. -/
theorem graphRangeIso_over (W : U.Etale) :
    (graphHom j W).isoOpensRange.hom ≫ (graphRangeObject j W).hom = W.hom :=
  sorry

/-- The source of the graph is canonically its open range, over `U`. -/
def graphRangeIso (W : U.Etale) : W ≅ graphRangeObject j W :=
  MorphismProperty.Over.isoMk (graphHom j W).isoOpensRange (graphRangeIso_over j W)

variable [LocallyQuasiFinite j]

/-- The finite-support pair `(Z_φ, s_φ)` associated to a section on `W`: the
open graph of `W.hom` in `U ×_X W`, with the section transported along the
range isomorphism. -/
def graphTerm (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) (W : U.Etale)
    (s : F.obj.obj (op W)) :
    FiniteSupportTerm j F ((etaleRestriction j).obj W) := by
  refine FiniteSupportTerm.of j F ((etaleRestriction j).obj W) W.left (graphHom j W)
    (graphHom j W).opensRange ?_ ?_
    ((F.obj.map (graphRangeIso j W).inv.op).hom s) ?_
  all_goals sorry

/-- An admissible graph pair records the graph immersion, its open range, and
the transported section. -/
theorem graphTerm_spec (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (W : U.Etale) (s : F.obj.obj (op W)) :
    (graphTerm j F W s).ι = graphHom j W ∧
      (graphTerm j F W s).ambient = (graphHom j W).opensRange ∧
      (graphTerm j F W s).sec = (F.obj.map (graphRangeIso j W).inv.op).hom s :=
  ⟨rfl, rfl, rfl⟩

/-- The objectwise graph coprojection `F(W) ⟶ f_{p!} F(j(W))`. -/
def extensionByZeroUnitApp (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (W : U.Etale) :
    F.obj.obj (op W) ⟶
      ((lowerShriekPresheaf j).obj F).obj (op ((etaleRestriction j).obj W)) := by
  refine AddCommGrpCat.ofHom
    { toFun := fun s ↦
        ofTerm j F ((etaleRestriction j).obj W) (graphTerm j F W s)
      map_zero' := ?_
      map_add' := ?_ }
  all_goals sorry

/-- The objectwise graph coprojection sends a section to the colimit class of
its graph pair. -/
theorem extensionByZeroUnitApp_apply
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) (W : U.Etale)
    (s : F.obj.obj (op W)) :
    (extensionByZeroUnitApp j F W).hom s =
      ofTerm j F ((etaleRestriction j).obj W) (graphTerm j F W s) :=
  rfl

/-- The lan-adjunction unit sending a section on `W` to the graph pair in
`f_{p!} F(j(W))`. -/
def extensionByZeroUnit (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :
    F.obj ⟶ (etaleRestriction j).op ⋙ (lowerShriekPresheaf j).obj F where
  app W := extensionByZeroUnitApp j F W.unop
  naturality := sorry

/-- The lan unit at `W` is the graph coprojection. -/
theorem extensionByZeroUnit_app (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (W : U.Etale) :
    (extensionByZeroUnit j F).app (op W) = extensionByZeroUnitApp j F W :=
  rfl

/-- Evaluating the lan unit at a section recovers the colimit class of the
graph pair. -/
theorem extensionByZeroUnit_app_apply
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) (W : U.Etale)
    (s : F.obj.obj (op W)) :
    ((extensionByZeroUnit j F).app (op W)).hom s =
      ofTerm j F ((etaleRestriction j).obj W) (graphTerm j F W s) :=
  rfl

variable
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension F]

/-- The canonical comparison of abelian presheaves `j_{p!} ⟶ f_{p!}`, obtained
by left Kan extending the graph unit along `(etaleRestriction j).op`. -/
def extensionByZeroToLowerShriekPresheaf :
    sheafToPresheaf U.smallEtaleTopology AddCommGrpCat.{u} ⋙
        (etaleRestriction j).op.lan ⟶
      lowerShriekPresheaf j where
  app F :=
    (((etaleRestriction j).op.lanAdjunction AddCommGrpCat.{u}).homEquiv
        F.obj ((lowerShriekPresheaf j).obj F)).symm
      (extensionByZeroUnit j F)
  naturality := sorry

/-- The presheaf comparison at `F` is the lan-adjunction transpose of the graph
unit. -/
theorem extensionByZeroToLowerShriekPresheaf_app
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :
    (extensionByZeroToLowerShriekPresheaf j).app F =
      (((etaleRestriction j).op.lanAdjunction AddCommGrpCat.{u}).homEquiv
          F.obj ((lowerShriekPresheaf j).obj F)).symm
        (extensionByZeroUnit j F) :=
  rfl

variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]

/-- The sheafified comparison `j_! ⟶ (f_{p!})^#`, obtained by transporting the
presheaf graph map across `sheafPullbackIso` and sheafification. -/
def extensionByZeroToLowerShriek :
    abelianExtensionByZero j ⟶
      lowerShriekPresheaf j ⋙
        presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (sheafPullbackConstruction.sheafPullbackIso (etaleRestriction j)
        AddCommGrpCat.{u} U.smallEtaleTopology X.smallEtaleTopology).hom ≫
    whiskerRight (extensionByZeroToLowerShriekPresheaf j)
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u})

/-- The sheafified comparison is `sheafPullbackIso.hom` followed by the
sheafified graph map. -/
theorem extensionByZeroToLowerShriek_hom :
    extensionByZeroToLowerShriek j =
      (sheafPullbackConstruction.sheafPullbackIso (etaleRestriction j)
            AddCommGrpCat.{u} U.smallEtaleTopology X.smallEtaleTopology).hom ≫
        whiskerRight (extensionByZeroToLowerShriekPresheaf j)
          (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  rfl

/-- The sheafified graph comparison `j_! ⟶ (f_{p!})^#` is an isomorphism. -/
instance extensionByZeroToLowerShriek_isIso :
    IsIso (extensionByZeroToLowerShriek j) :=
  sorry

/-- Étale extension by zero is naturally isomorphic to the sheafification of
the finite-support lower-shriek presheaf. -/
def extensionByZeroIsoLowerShriek :
    abelianExtensionByZero j ≅
      lowerShriekPresheaf j ⋙
        presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  asIso (extensionByZeroToLowerShriek j)

/-- The forward map of `extensionByZeroIsoLowerShriek` is the sheafified graph
comparison. -/
theorem extensionByZeroIsoLowerShriek_hom :
    (extensionByZeroIsoLowerShriek j).hom = extensionByZeroToLowerShriek j :=
  rfl

end AlgebraicGeometry.Scheme.Etale

end
