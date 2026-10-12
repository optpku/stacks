/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_11_2_RestrictionMonoidal
public import stacks_project.Chap66.«66_26_0_1_Pushforward»

/-!
# The represented-scheme direct-image square

Evaluation of direct image on an open is evaluation on its inverse image.
Here that map is an actual projection from the right-Kan-extension limit at
the scheme representing the inverse image open. Its adjoint gives the module
inverse-image comparison without equating differently presented objects.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf.InternalModule
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open RingedSite.ToposHom
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

variable {S : Scheme.{u}} {T Z : Over S}

/-- The restricted scheme morphism between the actual site objects. -/
def preimageOpenMap (t : T ⟶ Z) (V : Z.left.Opens) :
    (siteObject T (t.left ⁻¹ᵁ V)).left ⟶ (siteObject Z V).left :=
  Over.homMk (t.left.resLE V (t.left ⁻¹ᵁ V) le_rfl) sorry

/-- The inverse image open maps to the functor-of-points fibre product. -/
def preimageGraph (t : T ⟶ Z) (V : Z.left.Opens) :
    ofOver (siteObject T (t.left ⁻¹ᵁ V)).left ⟶
      etaleBaseChangeSpace (ofOverMap t) (siteObject Z V) :=
  pullback.lift (f := homFunctor (ofOverMap t))
    (g := homFunctor (siteObject Z V).hom)
    (siteObject T (t.left ⁻¹ᵁ V)).hom (ofOverMap (preimageOpenMap t V)) sorry

/-- The same graph as an arrow of etale algebraic spaces over the source. -/
def preimageGraphOver (t : T ⟶ Z) (V : Z.left.Opens) :
    (smallEtaleInclusion (ofOver T)).obj (siteObject T (t.left ⁻¹ᵁ V)) ⟶
      (etaleBaseChange (ofOverMap t)).obj (siteObject Z V) :=
  MorphismProperty.Over.homMk (preimageGraph t V) sorry

/-- The concrete index of the Kan-extension limit at an inverse image open. -/
def preimageGraphArrow (t : T ⟶ Z) (V : Z.left.Opens) :
    StructuredArrow (op ((etaleBaseChange (ofOverMap t)).obj (siteObject Z V)))
      (smallEtaleInclusion (ofOver T)).op :=
  StructuredArrow.mk (op (preimageGraphOver t V))

/-- The actual right-Kan-extension diagram defining direct-image sections. -/
abbrev pushforwardRanDiagram (t : T ⟶ Z) (M : (ofOver T).Modules)
    (V : Z.left.Opens) :=
  StructuredArrow.proj
      (op ((etaleBaseChange (ofOverMap t)).obj (siteObject Z V)))
      (smallEtaleInclusion (ofOver T)).op ⋙
    ((ToInternal.underlying (structureSheaf (ofOver T))).obj M).obj

instance pushforwardRanDiagram_hasLimit (t : T ⟶ Z) (M : (ofOver T).Modules)
    (V : Z.left.Opens) : HasLimit (pushforwardRanDiagram t M V) :=
  smallEtaleInclusion_op_hasPointwiseRightKanExtension_type (ofOver T)
    (((ToInternal.underlying (structureSheaf (ofOver T))).obj M).obj)
    (op ((etaleBaseChange (ofOverMap t)).obj (siteObject Z V)))

/-- Direct-image sections evaluated at the inverse image open, by a limit projection. -/
def pushforwardSection (t : T ⟶ Z) (M : (ofOver T).Modules) (V : Z.left.Opens)
    (x : ((Modules.restrictToScheme Z).obj
      ((Modules.pushforward (ofOverMap t)).obj M)).val.obj (op V)) :
    ((Modules.restrictToScheme T).obj M).val.obj (op (t.left ⁻¹ᵁ V)) :=
  (sectionEquiv T M (t.left ⁻¹ᵁ V)).symm
    ((ToInternal.sectionEquiv (structureSheaf (ofOver T)) M
      (op (siteObject T (t.left ⁻¹ᵁ V)))).symm
        (EtaleTopos.extensionEvaluation (ofOver T)
          ((ToInternal.underlying (structureSheaf (ofOver T))).obj M)
          (preimageGraphOver t V)
          ((((ModulePushforward.forgetIso (ringedToposHom (ofOverMap t))).hom.app M).hom.app
            (op (siteObject Z V)))
            (ToInternal.sectionEquiv (structureSheaf (ofOver Z))
              ((Modules.pushforward (ofOverMap t)).obj M) (op (siteObject Z V))
              (sectionEquiv Z _ V x)))))

/-- The scheme direct image evaluates at the same inverse image open. -/
def schemePushforwardSectionEquiv (t : T ⟶ Z) (M : T.left.Modules)
    (V : Z.left.Opens) :
    ((Scheme.Modules.pushforward t.left).obj M).val.obj (op V) ≃
      M.val.obj (op (t.left ⁻¹ᵁ V)) := Equiv.refl _

/-- The direct-image comparison as an actual module morphism. -/
def pushforwardComparisonApp (t : T ⟶ Z) (M : (ofOver T).Modules) :
    (Modules.restrictToScheme Z).obj ((Modules.pushforward (ofOverMap t)).obj M) ⟶
      (Scheme.Modules.pushforward t.left).obj ((Modules.restrictToScheme T).obj M) where
  val :=
    { app := fun V ↦ by
        let A := ((Modules.restrictToScheme Z).obj
            ((Modules.pushforward (ofOverMap t)).obj M)).val.obj V
        let B := ((Scheme.Modules.pushforward t.left).obj
            ((Modules.restrictToScheme T).obj M)).val.obj V
        -- Local instance justification (defeq pin): A retains the bundled source section action.
        letI := A.isModule
        -- Local instance justification (defeq pin): B retains the direct-image target section action.
        letI := B.isModule
        exact @ModuleCat.ofHom (Z.left.ringCatSheaf.obj.obj V) _ A B
          A.isAddCommGroup A.isModule B.isAddCommGroup B.isModule
          (show A →ₗ[Z.left.ringCatSheaf.obj.obj V] B from
        { toFun := fun x ↦ (schemePushforwardSectionEquiv t _ V.unop).symm
            (pushforwardSection t M V.unop x)
          map_add' := sorry
          map_smul' := sorry })
      naturality := sorry }

/-- Naturality of the direct-image square. -/
def pushforwardComparison (t : T ⟶ Z) :
    Modules.pushforward (ofOverMap t) ⋙ Modules.restrictToScheme Z ⟶
      Modules.restrictToScheme T ⋙ Scheme.Modules.pushforward t.left where
  app := pushforwardComparisonApp t
  naturality := sorry

/-- Evaluation at the inverse image open identifies the two direct images. -/
instance pushforwardComparison_isIso (t : T ⟶ Z) :
    IsIso (pushforwardComparison t) := sorry

/-- The canonical direct-image square, with the specified evaluation map. -/
def pushforwardComparisonIso (t : T ⟶ Z) :
    Modules.pushforward (ofOverMap t) ⋙ Modules.restrictToScheme Z ≅
      Modules.restrictToScheme T ⋙ Scheme.Modules.pushforward t.left :=
  asIso (pushforwardComparison t)

/-- Inverse images commute with extension, by uniqueness of their actual adjunctions. -/
def extensionPullbackIso (t : T ⟶ Z) :
    Scheme.Modules.pullback t.left ⋙ extension T ≅
      extension Z ⋙ Modules.pullback (ofOverMap t) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction t.left).comp
      (extensionAdjunction T)).leftAdjointUniq
    (((extensionAdjunction Z).comp
      (Modules.pullbackPushforwardAdjunction (ofOverMap t))).ofNatIsoRight
        (pushforwardComparisonIso t))

end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
