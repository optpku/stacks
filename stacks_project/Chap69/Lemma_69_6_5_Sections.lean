module

public import Mathlib.Data.Finite.Card
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap66.Lemma_66_18_12_Comparison
public import stacks_project.Chap69.Definition_69_6_2_Koszul
public import stacks_project.Chap69.Lemma_69_6_5_Quotient
public import stacks_project.Chap69.Lemma_69_6_5_Regular

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open SheafOfModules.RingedSite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

/-- The actual inverse-image/direct-image adjunction on abelian étale sheaves. -/
def sheafInverseImageAdjunction {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    sheafInverseImage AddCommGrpCat.{u + 1} f ⊣ sheafPushforwardAbelian f :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (etaleBaseChange f) AddCommGrpCat.{u + 1} (smallEtaleTopology Y)
      (spacesEtaleTopology X)).comp
    ((smallEtaleInclusion X).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (spacesEtaleTopology X))

namespace CharacterSections
variable {W U : AlgebraicSpace S} (q : W ⟶ U)

/-- Scheme charts of the space-valued fibre over an étale object. -/
abbrev Charts (V : smallEtaleSite U) :=
  StructuredArrow (op ((etaleBaseChange q).obj V)) (smallEtaleInclusion W).op

/-- The right-Kan-extension evaluation at a scheme chart. -/
def chartValue (H : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1})
    (V : smallEtaleSite U) (c : Charts q V)
    (s : ((sheafPushforwardAbelian q).obj H).obj.obj (op V)) : H.obj.obj c.right :=
  (((smallEtaleInclusion W).op.ran.obj H.obj).map c.hom ≫
    ((smallEtaleInclusion W).op.ranCounit.app H.obj).app c.right) s

/-- The chart's second projection, represented by the fully faithful Yoneda functor. -/
def chartToBase [Etale q] (V : smallEtaleSite U) (c : Charts q V) :
    (etaleRestriction q).obj c.right.unop ⟶ V :=
  MorphismProperty.CostructuredArrow.homMk
    (yoneda.preimage (c.hom.unop.left ≫ etaleBaseChangeSnd q V)) trivial sorry

/-- Multiply a sheaf section by a locally constant integer section through its
canonical module over the constant integer ring sheaf. -/
def integerMul (H : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1})
    (T : (smallEtaleSite W)ᵒᵖ) (n : (constantIntegerSheaf W).obj.obj T)
    (s : H.obj.obj T) : H.obj.obj T :=
  let a : (integerRingSheaf W).obj.obj T := (unitAbelianIso W).inv.hom.app T n
  let t : (abelianSheaf_integerModules H).val.obj T :=
    (abelianSheaf_integerModules_toSheafIso H).inv.hom.app T s
  (abelianSheaf_integerModules_toSheafIso H).hom.hom.app T
    (a • t)

/-- The compatible chart family representing the product of a base section
with a section of the pushed constant sheaf. -/
def productCone [Etale q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (V : smallEtaleSite U)
    (s : F.obj.obj (op V))
    (n : ((sheafPushforwardAbelian q).obj (constantIntegerSheaf W)).obj.obj (op V)) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange q).obj V))
      (smallEtaleInclusion W).op ⋙
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F).obj) where
  pt := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  π :=
    { app := fun c ↦ AddCommGrpCat.ofHom
        { toFun := fun z ↦ z.down •
            integerMul ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) c.right
              (chartValue q (constantIntegerSheaf W) V c n)
              (F.obj.map (chartToBase q V c).op s)
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }

/-- Descend the actual chart products through the pointwise right-Kan limit. -/
def product [Etale q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (V : smallEtaleSite U)
    (s : F.obj.obj (op V))
    (n : ((sheafPushforwardAbelian q).obj (constantIntegerSheaf W)).obj.obj (op V)) :
    ((sheafPushforwardAbelian q).obj
      ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)).obj.obj (op V) :=
  (((smallEtaleInclusion W).op.isPointwiseRightKanExtensionRanCounit
      ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F).obj
      (op ((etaleBaseChange q).obj V))).lift (productCone q F V s n)) (ULift.up 1)

/-- The limit lift has the prescribed value on every chart, so the projection
pairing uses the supplied section rather than a chosen constant or zero. -/
theorem product_chart [Etale q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (V : smallEtaleSite U)
    (s : F.obj.obj (op V))
    (n : ((sheafPushforwardAbelian q).obj (constantIntegerSheaf W)).obj.obj (op V))
    (c : Charts q V) :
    chartValue q ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) V c
        (product q F V s n) =
      integerMul ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) c.right
        (chartValue q (constantIntegerSheaf W) V c n)
        (F.obj.map (chartToBase q V c).op s) := sorry

/-- Bilinear projection pairing in the canonical integer-module presentations. -/
def projectionBilinear [Etale q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    SectionBilinearMap (J := smallEtaleTopology U) (constantIntegerRingSheaf U)
      (abelianSheaf_integerModules F)
      (abelianSheaf_integerModules ((sheafPushforwardAbelian q).obj (constantIntegerSheaf W)))
      (abelianSheaf_integerModules ((sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F))) where
  app V :=
    { toFun := fun s ↦
        { toFun := fun n ↦
            (abelianSheaf_integerModules_toSheafIso _).inv.hom.app V
              (product q F V.unop
                ((abelianSheaf_integerModules_toSheafIso F).hom.hom.app V s)
                ((abelianSheaf_integerModules_toSheafIso _).hom.hom.app V n))
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
  naturality := sorry

/-- The canonical projection morphism: sheafify the chartwise bilinear pairing. -/
def projectionHom [Etale q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (SheafOfModules.toSheaf (integerRingSheaf U)).obj
      (MonoidalCategory.tensorObj (abelianSheaf_integerModules F)
        (abelianSheaf_integerModules ((sheafPushforwardAbelian q).obj (constantIntegerSheaf W)))) ⟶
      (sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) :=
  (SheafOfModules.toSheaf (integerRingSheaf U)).map (projectionBilinear q F).hom ≫
    (abelianSheaf_integerModules_toSheafIso _).hom

/-- The constant integer section, simultaneously on all scheme charts. -/
def constantCone (V : smallEtaleSite U) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange q).obj V))
      (smallEtaleInclusion W).op ⋙ (constantIntegerSheaf W).obj) where
  pt := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  π :=
    { app := fun c ↦ (toSheafify (smallEtaleTopology W)
        ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app c.right
      naturality := sorry }

/-- Constants on the base map to constants on each chart of its inverse image. -/
def constantPresheafHom :
    (Functor.const (smallEtaleSite U)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      ((sheafPushforwardAbelian q).obj (constantIntegerSheaf W)).obj where
  app V := ((smallEtaleInclusion W).op.isPointwiseRightKanExtensionRanCounit
      (constantIntegerSheaf W).obj (op ((etaleBaseChange q).obj V.unop))).lift
        (constantCone q V.unop)
  naturality := sorry

/-- The sheafification adjunct of the genuine constant-section map. -/
def constantSheafHom :
    constantIntegerSheaf U ⟶ (sheafPushforwardAbelian q).obj (constantIntegerSheaf W) :=
  ((sheafificationAdjunction (smallEtaleTopology U) AddCommGrpCat.{u + 1}).homEquiv
    _ _).symm (constantPresheafHom q)

/-- The inverse-image constant comparison is the adjoint of chartwise constants. -/
def inverseImageConstantHom :
    (sheafInverseImage AddCommGrpCat.{u + 1} q).obj (constantIntegerSheaf U) ⟶
      constantIntegerSheaf W :=
  ((sheafInverseImageAdjunction q).homEquiv _ _).symm (constantSheafHom q)

/-- Inverse image of a constant sheaf preserves its coefficients; this applies
to the specified chartwise constant comparison, not to an object equality. -/
instance inverseImageConstantHom_isIso : IsIso (inverseImageConstantHom q) := sorry

/-- Finite sum over a `Finite` index type, using `Finite.equivFin`. -/
def finiteSum {α : Type*} [AddCommMonoid α] {ι : Type*} [Finite ι] (f : ι → α) : α :=
  (Finset.univ : Finset (Fin (Nat.card ι))).sum
    fun n ↦ f ((Finite.equivFin ι).symm n)

variable [Etale q]

/-- The identity section of the torsor fibre `T ×_U W` over a scheme étale over `W`. -/
def identitySection (T : smallEtaleSite W) :
    ofOver T.left ⟶ etaleBaseChangeSpace q ((etaleRestriction q).obj T) :=
  pullback.lift (homFunctor T.hom) (𝟙 (ofOver T.left)) sorry

/-- The identity graph of a scheme étale over `W`, as a torsor chart of `T ×_U W`. -/
def identityChart (T : smallEtaleSite W) :
    Charts q ((etaleRestriction q).obj T) :=
  StructuredArrow.mk (Y := op T)
    (MorphismProperty.Over.homMk (identitySection q T) sorry).op

/-- Evaluation of a pushforward section at the identity graph after the torsor
chart `T → W`. This is the identity coordinate of the regular representation. -/
def pushforwardEvalIdentity
    (H : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1})
    (T : smallEtaleSite W)
    (s : ((sheafPushforwardAbelian q).obj H).obj.obj
      (op ((etaleRestriction q).obj T))) :
    H.obj.obj (op T) :=
  chartValue q H ((etaleRestriction q).obj T) (identityChart q T) s

/-- A chart of `T ×_U W` lies on the identity graph when its structure map to `W`
factors as the second projection followed by `T ⟶ W`. -/
def chartIsIdentityGraph (T : smallEtaleSite W)
    (c : Charts q ((etaleRestriction q).obj T)) : Prop :=
  (ofOverFunctor S).map (chartToBase q ((etaleRestriction q).obj T) c).left ≫ T.hom =
    c.right.unop.hom

/-- Coefficient `1` on the identity graph and `0` on every other torsor chart. -/
def identityIndicatorCoeff (T : smallEtaleSite W)
    (c : Charts q ((etaleRestriction q).obj T)) : ℤ :=
  have := Classical.propDecidable (chartIsIdentityGraph q T c)
  if chartIsIdentityGraph q T c then 1 else 0

/-- The family of scheme charts of `W ×_U V` covers `V` because `q` is étale
and surjective. -/
theorem charts_cover [Surjective q] (V : smallEtaleSite U) :
    Sieve.ofArrows (fun c : Charts q V ↦ (etaleRestriction q).obj c.right.unop)
      (fun c ↦ chartToBase q V c) ∈ smallEtaleTopology U V :=
  sorry

end CharacterSections
end AlgebraicGeometry.AlgebraicSpace
