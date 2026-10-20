module

public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.EtaleBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Exact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IntegerModules
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.GlobalSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FreeQuotient.Torsor

/-! # Integer projection formula for finite torsors -/

@[expose] public section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory Opposite SheafOfModules.RingedSite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

/-- Inverse image is left adjoint to direct image for abelian étale sheaves. -/
def sheafInverseImageAdjunction {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    sheafInverseImage AddCommGrpCat.{u + 1} f ⊣ sheafPushforwardAbelian f :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (etaleBaseChange f) AddCommGrpCat.{u + 1} (smallEtaleTopology Y)
      (spacesEtaleTopology X)).comp
    ((smallEtaleToSpaces X).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology X) (spacesEtaleTopology X))

namespace CharacterSections
variable {W U : AlgebraicSpace S} (q : W ⟶ U)

/-- Scheme charts of the space-valued fibre over an étale object. -/
abbrev Charts (V : smallEtaleSite U) :=
  StructuredArrow (op ((etaleBaseChange q).obj V)) (smallEtaleToSpaces W).op

/-- The right-Kan-extension evaluation at a scheme chart. -/
def chartValue (H : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1})
    (V : smallEtaleSite U) (c : Charts q V)
    (s : ((sheafPushforwardAbelian q).obj H).obj.obj (op V)) : H.obj.obj c.right :=
  (((smallEtaleToSpaces W).op.ran.obj H.obj).map c.hom ≫
    ((smallEtaleToSpaces W).op.ranCounit.app H.obj).app c.right) s

/-- The chart's second projection, represented by the fully faithful Yoneda functor. -/
def chartToBase [Etale q] (V : smallEtaleSite U) (c : Charts q V) :
    (etaleRestriction q).obj c.right.unop ⟶ V :=
  MorphismProperty.CostructuredArrow.homMk
    (yoneda.preimage (c.hom.unop.left ≫ etaleBaseChangeSnd q V)) trivial sorry

/-- Multiply a sheaf section by a locally constant integer section through its
canonical module over the constant integer ring sheaf. -/
def integerMul (H : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1})
    (T : (smallEtaleSite W)ᵒᵖ) (n : (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)).obj.obj T)
    (s : H.obj.obj T) : H.obj.obj T :=
  let a : (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf W)).obj.obj T := (unitAbelianIso W).inv.hom.app T n
  let t : (abelianSheaf_integerModules H).val.obj T :=
    (abelianSheaf_integerModules_toSheafIso H).inv.hom.app T s
  (abelianSheaf_integerModules_toSheafIso H).hom.hom.app T
    (a • t)

/-- The compatible chart family representing the product of a base section
with a section of the pushed constant sheaf. -/
def productCone [Etale q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (V : smallEtaleSite U)
    (s : F.obj.obj (op V))
    (n : ((sheafPushforwardAbelian q).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W))).obj.obj (op V)) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange q).obj V))
      (smallEtaleToSpaces W).op ⋙
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F).obj) where
  pt := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  π :=
    { app := fun c ↦ AddCommGrpCat.ofHom
        { toFun := fun z ↦ z.down •
            integerMul ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) c.right
              (chartValue q (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)) V c n)
              (F.obj.map (chartToBase q V c).op s)
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }

/-- Descend the actual chart products through the pointwise right-Kan limit. -/
def product [Etale q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (V : smallEtaleSite U)
    (s : F.obj.obj (op V))
    (n : ((sheafPushforwardAbelian q).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W))).obj.obj (op V)) :
    ((sheafPushforwardAbelian q).obj
      ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)).obj.obj (op V) :=
  (((smallEtaleToSpaces W).op.isPointwiseRightKanExtensionRanCounit
      ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F).obj
      (op ((etaleBaseChange q).obj V))).lift (productCone q F V s n)) (ULift.up 1)

/-- The limit lift has the prescribed value on every chart, so the projection
pairing uses the supplied section rather than a chosen constant or zero. -/
theorem product_chart [Etale q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (V : smallEtaleSite U)
    (s : F.obj.obj (op V))
    (n : ((sheafPushforwardAbelian q).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W))).obj.obj (op V))
    (c : Charts q V) :
    chartValue q ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) V c
        (product q F V s n) =
      integerMul ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) c.right
        (chartValue q (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)) V c n)
        (F.obj.map (chartToBase q V c).op s) := sorry

/-- Bilinear projection pairing in the canonical integer-module presentations. -/
def projectionBilinear [Etale q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    SectionBilinearMap (J := smallEtaleTopology U) (constantIntegerRingSheaf U)
      (abelianSheaf_integerModules F)
      (abelianSheaf_integerModules ((sheafPushforwardAbelian q).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W))))
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
    (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf U))).obj
      (MonoidalCategory.tensorObj (abelianSheaf_integerModules F)
        (abelianSheaf_integerModules ((sheafPushforwardAbelian q).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W))))) ⟶
      (sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) :=
  (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf U))).map (projectionBilinear q F).hom ≫
    (abelianSheaf_integerModules_toSheafIso _).hom

/-- The constant integer section, simultaneously on all scheme charts. -/
def constantCone (V : smallEtaleSite U) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange q).obj V))
      (smallEtaleToSpaces W).op ⋙ (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)).obj) where
  pt := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  π :=
    { app := fun c ↦ (toSheafify (smallEtaleTopology W)
        ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app c.right
      naturality := sorry }

/-- Constants on the base map to constants on each chart of its inverse image. -/
def constantPresheafHom :
    (Functor.const (smallEtaleSite U)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      ((sheafPushforwardAbelian q).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W))).obj where
  app V := ((smallEtaleToSpaces W).op.isPointwiseRightKanExtensionRanCounit
      (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)).obj (op ((etaleBaseChange q).obj V.unop))).lift
        (constantCone q V.unop)
  naturality := sorry

/-- The sheafification adjunct of the genuine constant-section map. -/
def constantSheafHom :
    (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology U)) ⟶ (sheafPushforwardAbelian q).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)) :=
  ((sheafificationAdjunction (smallEtaleTopology U) AddCommGrpCat.{u + 1}).homEquiv
    _ _).symm (constantPresheafHom q)

/-- The inverse-image constant comparison is the adjoint of chartwise constants. -/
def inverseImageConstantHom :
    (sheafInverseImage AddCommGrpCat.{u + 1} q).obj
      (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology U)) ⟶
      CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W) :=
  ((sheafInverseImageAdjunction q).homEquiv _ _).symm (constantSheafHom q)

/-- The chartwise comparison between inverse image of constant integers and
constant integers is invertible. -/
instance inverseImageConstantHom_isIso : IsIso (inverseImageConstantHom q) := sorry

section EtaleCharts
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

end EtaleCharts

variable {G : Type u} [Group G] [Finite G]

/-- A torsor chart gives a morphism into the specified shear fibre product. -/
def chartPair (ρ : G →* Aut W) [IsFreeQuotient ρ q] (T : smallEtaleSite W)
    (c : Charts q ((etaleRestriction q).obj T)) :
    ofOver c.right.unop.left ⟶ pullback q q :=
  pullback.lift c.right.unop.hom
    ((ofOverFunctor S).map (chartToBase q ((etaleRestriction q).obj T) c).left ≫ T.hom)
    sorry

/-- The actual G-labelled clopen decomposition of a chart, obtained from the
inverse of the caller-specified torsor shear. -/
def chartPartition (ρ : G →* Aut W) [IsFreeQuotient ρ q] (T : smallEtaleSite W)
    (c : Charts q ((etaleRestriction q).obj T)) :
    CoproductSection (fun _ : G ↦ W) c.right.unop.left :=
  let quotient : IsFreeQuotient ρ q := inferInstance
  let shearInv : pullback q q ⟶ coproduct (fun _ : G ↦ W) :=
    @CategoryTheory.inv (AlgebraicSpace S) _ _ _
      (shear ρ q quotient.smul_comp) quotient.isIso_shear
  let lift : ofOver c.right.unop.left ⟶ coproduct (fun _ : G ↦ W) :=
    chartPair q ρ T c ≫ shearInv
  yonedaEquiv lift

/-- The scheme over S underlying a labelled clopen piece of the chart. -/
def chartPieceOver (ρ : G →* Aut W) [IsFreeQuotient ρ q] (T : smallEtaleSite W)
    (c : Charts q ((etaleRestriction q).obj T)) (g : G) : Over S :=
  Over.mk (((chartPartition q ρ T c).piece (equivShrink.{u} G g)).ι ≫
    c.right.unop.left.hom)

/-- The actual open-immersion arrow from a labelled piece into its chart. -/
def chartPieceOverHom (ρ : G →* Aut W) [IsFreeQuotient ρ q] (T : smallEtaleSite W)
    (c : Charts q ((etaleRestriction q).obj T)) (g : G) :
    chartPieceOver q ρ T c g ⟶ c.right.unop.left :=
  Over.homMk (((chartPartition q ρ T c).piece (equivShrink.{u} G g)).ι) sorry

/-- The structure morphism of the chart's g-labelled clopen piece. -/
def chartPieceStructure (ρ : G →* Aut W) [IsFreeQuotient ρ q] (T : smallEtaleSite W)
    (c : Charts q ((etaleRestriction q).obj T)) (g : G) :
    ofOver (chartPieceOver q ρ T c g) ⟶ W :=
  ofOverMap (chartPieceOverHom q ρ T c g) ≫ c.right.unop.hom

/-- A clopen piece of an étale chart is still étale over W. -/
theorem chartPieceStructure_etale (ρ : G →* Aut W) [IsFreeQuotient ρ q]
    (T : smallEtaleSite W) (c : Charts q ((etaleRestriction q).obj T)) (g : G) :
    Etale (chartPieceStructure q ρ T c g) := sorry

/-- The labelled clopen piece as an actual small étale object of W. -/
def chartPieceSite (ρ : G →* Aut W) [IsFreeQuotient ρ q] (T : smallEtaleSite W)
    (c : Charts q ((etaleRestriction q).obj T)) (g : G) : smallEtaleSite W :=
  MorphismProperty.CostructuredArrow.mk ⊤ (chartPieceStructure q ρ T c g)
    (chartPieceStructure_etale q ρ T c g)

/-- The inclusion of the actual labelled clopen piece into its chart. -/
def chartPieceHom (ρ : G →* Aut W) [IsFreeQuotient ρ q] (T : smallEtaleSite W)
    (c : Charts q ((etaleRestriction q).obj T)) (g : G) :
    chartPieceSite q ρ T c g ⟶ c.right.unop :=
  MorphismProperty.CostructuredArrow.homMk (chartPieceOverHom q ρ T c g) trivial sorry

/-- All clopen pieces, including empty pieces, cover the original chart. -/
theorem chartPieces_cover (ρ : G →* Aut W) [IsFreeQuotient ρ q]
    (T : smallEtaleSite W) (c : Charts q ((etaleRestriction q).obj T)) :
    Sieve.ofArrows (fun g ↦ chartPieceSite q ρ T c g)
      (fun g ↦ chartPieceHom q ρ T c g) ∈ smallEtaleTopology W c.right.unop := sorry

/-- The identity coefficient on one labelled clopen piece:1 at the identity label,0 elsewhere. -/
def identityPieceCoeff (ρ : G →* Aut W) [IsFreeQuotient ρ q] (T : smallEtaleSite W)
    (c : Charts q ((etaleRestriction q).obj T)) (g : G) :
    AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶
      (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)).obj.obj (op (chartPieceSite q ρ T c g)) := by
  classical
  exact AddCommGrpCat.ofHom
    { toFun := fun z ↦
        (toSheafify (smallEtaleTopology W)
          ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
          (op (chartPieceSite q ρ T c g))
          (ULift.up (z.down * if g = 1 then 1 else 0))
      map_zero' := sorry
      map_add' := sorry }

/-- The locally constant labelled coefficients agree on all clopen overlaps. -/
theorem identityPieceCoeff_compatible (ρ : G →* Aut W) [IsFreeQuotient ρ q]
    (T : smallEtaleSite W) (c : Charts q ((etaleRestriction q).obj T)) :
    ∀ ⦃V : smallEtaleSite W⦄ ⦃g h : G⦄
      (a : V ⟶ chartPieceSite q ρ T c g) (b : V ⟶ chartPieceSite q ρ T c h),
      a ≫ chartPieceHom q ρ T c g = b ≫ chartPieceHom q ρ T c h →
        identityPieceCoeff q ρ T c g ≫ (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)).obj.map a.op =
          identityPieceCoeff q ρ T c h ≫ (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)).obj.map b.op := sorry

/-- The coefficient is a genuine locally constant integer section on the whole
chart, glued from the actual labelled pieces. -/
def identityIndicatorCoeff (ρ : G →* Aut W) [IsFreeQuotient ρ q]
    (T : smallEtaleSite W) (c : Charts q ((etaleRestriction q).obj T)) :
    (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)).obj.obj c.right :=
  ((CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)).property.amalgamateOfArrows
    (fun g ↦ chartPieceHom q ρ T c g) (chartPieces_cover q ρ T c)
    (fun g ↦ identityPieceCoeff q ρ T c g)
    (identityPieceCoeff_compatible q ρ T c)) (ULift.up 1)

/-- On every labelled piece, the glued coefficient has the specified0/1 value. -/
theorem identityIndicatorCoeff_piece (ρ : G →* Aut W) [IsFreeQuotient ρ q]
    (T : smallEtaleSite W) (c : Charts q ((etaleRestriction q).obj T)) (g : G) :
    (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)).obj.map (chartPieceHom q ρ T c g).op
        (identityIndicatorCoeff q ρ T c) =
      identityPieceCoeff q ρ T c g (ULift.up 1) := sorry

/-- The actual locally constant coefficient respects chart refinement. -/
theorem identityIndicatorCoeff_naturality (ρ : G →* Aut W) [IsFreeQuotient ρ q]
    (T : smallEtaleSite W) {c d : Charts q ((etaleRestriction q).obj T)} (f : c ⟶ d) :
    (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)).obj.map f.right (identityIndicatorCoeff q ρ T c) =
      identityIndicatorCoeff q ρ T d := sorry

/-- The family of scheme charts of `W ×_U V` covers `V` because `q` is étale
and surjective. -/
theorem charts_cover [Etale q] [Surjective q] (V : smallEtaleSite U) :
    Sieve.ofArrows (fun c : Charts q V ↦ (etaleRestriction q).obj c.right.unop)
      (fun c ↦ chartToBase q V c) ∈ smallEtaleTopology U V :=
  sorry

end CharacterSections

variable {W U : AlgebraicSpace S} {G : Type u} [Group G]

/-- Equal morphisms of algebraic spaces induce isomorphic étale restriction functors. -/
noncomputable def etaleRestrictionCongrIso {X Y : AlgebraicSpace S}
    {f f' : X ⟶ Y} [Etale f] [Etale f'] (h : f = f') :
    etaleRestriction f ≅ etaleRestriction f' :=
  NatIso.ofComponents
    (fun V =>
      MorphismProperty.CostructuredArrow.isoMk (Iso.refl V.left) trivial trivial sorry)
    sorry

/-- Étale restriction is functorial in the morphism, up to a canonical isomorphism
identity on the underlying scheme. -/
noncomputable def etaleRestrictionCompIso {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Etale f] [Etale g] :
    etaleRestriction (f ≫ g) ≅ etaleRestriction f ⋙ etaleRestriction g :=
  NatIso.ofComponents
    (fun V =>
      MorphismProperty.CostructuredArrow.isoMk (Iso.refl V.left) trivial trivial sorry)
    sorry

/-- Composite étale restriction functors are continuous. -/
instance etaleRestriction_comp_isContinuous {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Etale f] [Etale g] :
    (etaleRestriction f ⋙ etaleRestriction g).IsContinuous
      (smallEtaleTopology X) (smallEtaleTopology Z) :=
  Functor.isContinuous_comp (etaleRestriction f) (etaleRestriction g)
    (smallEtaleTopology X) (smallEtaleTopology Y) (smallEtaleTopology Z)


variable [finiteG : Finite G]

/-- Identification `(ρ g)^* (F|_W) ≅ F|_W` coming from `(ρ g).hom ≫ q = q`. -/
noncomputable def restrictionPastingIso (ρ : G →* Aut W) (q : W ⟶ U)
    [IsFreeQuotient ρ q] (g : G) :
    etaleRestrictionSheaf q AddCommGrpCat.{u + 1} ⋙
        etaleRestrictionSheaf (ρ g).hom AddCommGrpCat.{u + 1} ≅
      etaleRestrictionSheaf q AddCommGrpCat.{u + 1} :=
  Functor.sheafPushforwardContinuousComp (etaleRestriction (ρ g).hom)
      (etaleRestriction q) AddCommGrpCat.{u + 1} (smallEtaleTopology W)
      (smallEtaleTopology W) (smallEtaleTopology U) ≪≫
    Functor.sheafPushforwardContinuousIso (etaleRestrictionCompIso (ρ g).hom q).symm
      AddCommGrpCat.{u + 1} (smallEtaleTopology W) (smallEtaleTopology U) ≪≫
    Functor.sheafPushforwardContinuousIso
      (etaleRestrictionCongrIso (IsFreeQuotient.smul_comp g))
      AddCommGrpCat.{u + 1} (smallEtaleTopology W) (smallEtaleTopology U)

/-- The `G`-action on `H^0(W, F|_W)` by pullback along `(ρ (g⁻¹)).hom` and the
pasting identification over `U`, so that `G →* Aut` respects `Aut` multiplication. -/
noncomputable def globalSectionsAction (ρ : G →* Aut W) (q : W ⟶ U)
    [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    G →* Aut ((globalSections W).obj
      ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)) where
  toFun g :=
    { hom :=
        AddCommGrpCat.ofHom
          { toFun := fun s =>
              constantIntegerPullbackHom (ρ (g⁻¹)).hom ≫
                (etaleRestrictionSheaf (ρ (g⁻¹)).hom AddCommGrpCat.{u + 1}).map s ≫
                  (restrictionPastingIso ρ q (g⁻¹)).hom.app F
            map_zero' := sorry
            map_add' := sorry }
      inv :=
        AddCommGrpCat.ofHom
          { toFun := fun s =>
              constantIntegerPullbackHom (ρ g).hom ≫
                (etaleRestrictionSheaf (ρ g).hom AddCommGrpCat.{u + 1}).map s ≫
                  (restrictionPastingIso ρ q g).hom.app F
            map_zero' := sorry
            map_add' := sorry }
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- The identity square of a free quotient morphism is a pullback. -/
theorem isPullback_smul_comp (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (g : G) : IsPullback (ρ g).hom q q (𝟙 U) := sorry

/-- Restriction along an identity morphism is isomorphic to the identity functor
on abelian étale sheaves. -/
noncomputable def etaleRestrictionSheaf_idIso (X : AlgebraicSpace S) :
    etaleRestrictionSheaf (𝟙 X) AddCommGrpCat.{u + 1} ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (eqToIso (etaleRestriction_id X))
    AddCommGrpCat.{u + 1} (smallEtaleTopology X)

/-- Direct image `q_* ℤ̲` on `U_étale`. -/
noncomputable def pushforwardConstantInteger (q : W ⟶ U) :
    Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1} :=
  (sheafPushforwardAbelian q).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W))

/-- `pushforwardConstantInteger` is abelian sheaf pushforward of `ℤ̲_W`. -/
theorem pushforwardConstantInteger_def (q : W ⟶ U) :
    pushforwardConstantInteger q =
      (sheafPushforwardAbelian q).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)) := rfl

/-- The sheaf morphism `q_* ℤ̲ ⟶ q_* ℤ̲` by base change along `(ρ g).hom`. -/
noncomputable def pushforwardConstantIntegerSmul
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q] (g : G) :
    pushforwardConstantInteger q ⟶ pushforwardConstantInteger q :=
  (etaleRestrictionSheaf_idIso U).inv.app (pushforwardConstantInteger q) ≫
    pushforwardEtaleBaseChangeHom (isPullback_smul_comp ρ q g)
      AddCommGrpCat.{u + 1} (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)) ≫
      (sheafPushforwardAbelian q).map ((constantIntegerPullbackIso (ρ g).hom).inv)

/-- The identity of `G` acts by the identity on `q_* ℤ̲`. -/
theorem pushforwardConstantIntegerSmul_one
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q] :
    pushforwardConstantIntegerSmul ρ q (1 : G) = 𝟙 _ := sorry

/-- Pullback of sections is contravariant: the raw action of a product is
first pullback by g and then pullback by h, in categorical composition order. -/
theorem pushforwardConstantIntegerSmul_mul
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q] (g h : G) :
    pushforwardConstantIntegerSmul ρ q (g * h) =
      pushforwardConstantIntegerSmul ρ q g ≫
        pushforwardConstantIntegerSmul ρ q h := sorry

/-- The `G`-action on sections of `q_* ℤ̲` over an étale object of `U`.
The automorphism associated to `g` is pullback along `(ρ (g⁻¹)).hom`, so that
`G →* Aut` respects function-composition multiplication on `Aut`. -/
noncomputable def pushforwardConstantIntegerAction
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q] (V : smallEtaleSite U) :
    G →* Aut ((pushforwardConstantInteger q).obj.obj (op V)) where
  toFun g :=
    { hom := (pushforwardConstantIntegerSmul ρ q g⁻¹).hom.app (op V)
      inv := (pushforwardConstantIntegerSmul ρ q g).hom.app (op V)
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- Restriction of sections of `q_* ℤ̲` is G-equivariant. -/
theorem pushforwardConstantInteger_map_equivariant
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    {V V' : (smallEtaleSite U)ᵒᵖ} (f : V ⟶ V') (g : G) :
    ((pushforwardConstantIntegerAction ρ q (unop V)) g).hom ≫
        (pushforwardConstantInteger q).obj.map f =
      (pushforwardConstantInteger q).obj.map f ≫
        ((pushforwardConstantIntegerAction ρ q (unop V')) g).hom := sorry

/-- Functoriality of `abelianSheaf_integerModules` on morphisms of abelian sheaves. -/
noncomputable def abelianSheaf_integerModules_map {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    abelianSheaf_integerModules F ⟶ abelianSheaf_integerModules G :=
  (PresheafOfModules.sheafification (constantIntegerRingPresheafToSheaf X)).map
    (PresheafOfModules.homMk φ.hom sorry)

/-- The abelian sheaf `F ⊗_ℤ q_* ℤ̲` on `U_étale`. -/
noncomputable def tensorPushforwardConstantInteger (q : W ⟶ U)
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf U))).obj
    (tensorObj (abelianSheaf_integerModules F)
      (abelianSheaf_integerModules (pushforwardConstantInteger q)))

/-- The `G`-action on `F ⊗_ℤ q_* ℤ̲` by acting on `q_* ℤ̲`. -/
noncomputable def tensorPushforwardConstantIntegerSmul
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (g : G) :
    tensorPushforwardConstantInteger q F ⟶ tensorPushforwardConstantInteger q F :=
  (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf U))).map
    (tensorHom (𝟙 (abelianSheaf_integerModules F))
      (abelianSheaf_integerModules_map (pushforwardConstantIntegerSmul ρ q g)))

/-- The `G`-action on `H^0(U, F ⊗_ℤ q_* ℤ̲)`. -/
noncomputable def tensorPushforwardGlobalSectionsAction
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    G →* Aut ((globalSections U).obj (tensorPushforwardConstantInteger q F)) where
  toFun g :=
    { hom := (globalSections U).map (tensorPushforwardConstantIntegerSmul ρ q F g⁻¹)
      inv := (globalSections U).map (tensorPushforwardConstantIntegerSmul ρ q F g)
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- Counit of pushforward along a free-quotient torsor: evaluate at the identity
graph of the fibre `T ×_U W`. -/
noncomputable def pushforwardCounit (q : W ⟶ U) [Etale q]
    (H : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1}) :
    (etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj
        ((sheafPushforwardAbelian q).obj H) ⟶ H where
  hom :=
    { app T := AddCommGrpCat.ofHom
        { toFun := fun s ↦
            CharacterSections.pushforwardEvalIdentity q H T.unop s
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }

/-- The `G`-action on `q_* (F|_W)` by base change along `(ρ g).hom` and the
pasting identification over `U`. -/
noncomputable def restrictionPushforwardSmul
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (g : G) :
    (sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) ⟶
      (sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) :=
  (etaleRestrictionSheaf_idIso U).inv.app _ ≫
    pushforwardEtaleBaseChangeHom (isPullback_smul_comp ρ q g)
      AddCommGrpCat.{u + 1}
      ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) ≫
    (sheafPushforwardAbelian q).map ((restrictionPastingIso ρ q g).hom.app F)

/-- Identity-coordinate evaluation of a pushforward section of `F|_W`. -/
noncomputable def evalAtOne
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1})
    (T : smallEtaleSite W)
    (t : ((sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)).obj.obj
      (op ((etaleRestriction q).obj T))) :
    F.obj.obj (op ((etaleRestriction q).obj T)) :=
  CharacterSections.pushforwardEvalIdentity q
    ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) T t

/-- Evaluation after pullback by `g⁻¹` reads the `g⁻¹`-labelled sheet.
It matches the support of the pullback translate in `characterBasis`. -/
noncomputable def splitComponent
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1})
    (T : smallEtaleSite W) (g : G)
    (t : ((sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)).obj.obj
      (op ((etaleRestriction q).obj T))) :
    F.obj.obj (op ((etaleRestriction q).obj T)) :=
  evalAtOne ρ q F T
    ((restrictionPushforwardSmul ρ q F g⁻¹).hom.app
      (op ((etaleRestriction q).obj T)) t)

/-- The compatible identity-coordinate family uses locally constant sections on
mixed charts, with value1 on the identity-labelled piece and0 on other pieces. -/
noncomputable def identityBasisCone (ρ : G →* Aut W)
    (q : W ⟶ U) [IsFreeQuotient ρ q] (T : smallEtaleSite W) :
    Cone (StructuredArrow.proj
        (op ((etaleBaseChange q).obj ((etaleRestriction q).obj T)))
        (smallEtaleToSpaces W).op ⋙ (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)).obj) where
  pt := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  π :=
    { app := fun c ↦ AddCommGrpCat.ofHom
        { toFun := fun z ↦ z.down • CharacterSections.identityIndicatorCoeff q ρ T c
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }

/-- The identity basis section of the finite torsor pushforward, constructed
from its actual locally constant chart coefficients. -/
noncomputable def identityBasis (ρ : G →* Aut W)
    (q : W ⟶ U) [IsFreeQuotient ρ q] (T : smallEtaleSite W) :
    ((sheafPushforwardAbelian q).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W))).obj.obj
      (op ((etaleRestriction q).obj T)) :=
  (((smallEtaleToSpaces W).op.isPointwiseRightKanExtensionRanCounit
      (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W)).obj
      (op ((etaleBaseChange q).obj ((etaleRestriction q).obj T)))).lift
    (identityBasisCone ρ q T)) (ULift.up 1)

/-- Pullback of the identity basis along `g`, supported on the `g⁻¹`-labelled sheet. -/
noncomputable def characterBasis
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (T : smallEtaleSite W) (g : G) :
    ((sheafPushforwardAbelian q).obj (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology W))).obj.obj
      (op ((etaleRestriction q).obj T)) :=
  (pushforwardConstantIntegerSmul ρ q g).hom.app
    (op ((etaleRestriction q).obj T)) (identityBasis ρ q T)

include finiteG in
/-- Chartwise inverse of multiplication. Both `splitComponent g` and
`characterBasis g` use the `g⁻¹`-labelled sheet, so this sums each sheet once. -/
noncomputable def localTensor
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1})
    (T : smallEtaleSite W)
    (t : ((sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)).obj.obj
      (op ((etaleRestriction q).obj T))) :
    (tensorPushforwardConstantInteger q F).obj.obj
      (op ((etaleRestriction q).obj T)) :=
  let V := op ((etaleRestriction q).obj T)
  ((SheafOfModules.toSheafCompSheafToPresheafIso (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf U))).inv.app
    (tensorObj (abelianSheaf_integerModules F)
      (abelianSheaf_integerModules (pushforwardConstantInteger q)))).app V
    ((Finset.univ : Finset (Fin (Nat.card G))).sum fun n ↦
      let g : G := (Finite.equivFin G).symm n;
      tensorSection (constantIntegerRingSheaf U) V
        ((abelianSheaf_integerModules_toSheafIso F).inv.hom.app V
          (splitComponent ρ q F T g t))
        ((abelianSheaf_integerModules_toSheafIso
            (pushforwardConstantInteger q)).inv.hom.app V
          (characterBasis ρ q T g)))

/-- The forward identification `H^0(W, G) ⟶ H^0(U, q_* G)`. -/
noncomputable def globalSectionsPushforwardHom (q : W ⟶ U) [Etale q]
    (Gsh : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1}) :
    (globalSections W).obj Gsh ⟶
      (globalSections U).obj ((sheafPushforwardAbelian q).obj Gsh) :=
  AddCommGrpCat.ofHom
    { toFun := fun φ =>
        (sheafInverseImageAdjunction q).homEquiv (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology U)) Gsh
          (CharacterSections.inverseImageConstantHom q ≫ φ)
      map_zero' := sorry
      map_add' := sorry }

/-- The reverse identification `H^0(U, q_* G) ⟶ H^0(W, G)`, by restricting
along `q` and evaluating at the identity graph. -/
noncomputable def globalSectionsPushforwardInv (q : W ⟶ U) [Etale q]
    (Gsh : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1}) :
    (globalSections U).obj ((sheafPushforwardAbelian q).obj Gsh) ⟶
      (globalSections W).obj Gsh :=
  AddCommGrpCat.ofHom
    { toFun := fun ψ =>
        constantIntegerPullbackHom q ≫
          (etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).map ψ ≫
            pushforwardCounit q Gsh
      map_zero' := sorry
      map_add' := sorry }

/-- Global sections satisfy `H^0(W, G) ≅ H^0(U, q_* G)`. -/
noncomputable def globalSectionsPushforwardIso (q : W ⟶ U) [Etale q]
    (Gsh : Sheaf (smallEtaleTopology W) AddCommGrpCat.{u + 1}) :
    (globalSections W).obj Gsh ≅
      (globalSections U).obj ((sheafPushforwardAbelian q).obj Gsh) where
  hom := globalSectionsPushforwardHom q Gsh
  inv := globalSectionsPushforwardInv q Gsh
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The canonical projection morphism, defined on charts by multiplying the
restricted base section by the local integer coefficient. -/
noncomputable def projectionFormulaIntegerInv (q : W ⟶ U) [Etale q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    tensorPushforwardConstantInteger q F ⟶
      (sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) :=
  CharacterSections.projectionHom q F

include finiteG in
/-- The local inverse tensor formulas agree on overlaps of the actual torsor chart cover. -/
private theorem localTensor_compatible (ρ : G →* Aut W) (q : W ⟶ U)
    [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (V : smallEtaleSite U) :
    ∀ ⦃R : smallEtaleSite U⦄ ⦃c d : CharacterSections.Charts q V⦄
      (a : R ⟶ (etaleRestriction q).obj c.right.unop)
      (b : R ⟶ (etaleRestriction q).obj d.right.unop),
      a ≫ CharacterSections.chartToBase q V c = b ≫ CharacterSections.chartToBase q V d →
        ∀ t : ((sheafPushforwardAbelian q).obj
          ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)).obj.obj (op V),
        (tensorPushforwardConstantInteger q F).obj.map a.op
          (localTensor ρ q F c.right.unop
            (((sheafPushforwardAbelian q).obj
              ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)).obj.map
              (CharacterSections.chartToBase q V c).op t)) =
        (tensorPushforwardConstantInteger q F).obj.map b.op
          (localTensor ρ q F d.right.unop
            (((sheafPushforwardAbelian q).obj
              ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)).obj.map
              (CharacterSections.chartToBase q V d).op t)) := sorry

include finiteG in
/-- The forward projection formula is the actual finite-basis inverse, glued
over the torsor chart cover. -/
noncomputable def projectionFormulaIntegerHom (ρ : G →* Aut W) (q : W ⟶ U)
    [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) ⟶
      tensorPushforwardConstantInteger q F where
  hom :=
    { app := fun V ↦
        (tensorPushforwardConstantInteger q F).property.amalgamateOfArrows
          (fun c : CharacterSections.Charts q V.unop ↦
            CharacterSections.chartToBase q V.unop c)
          (CharacterSections.charts_cover q V.unop)
          (fun c ↦ AddCommGrpCat.ofHom
            { toFun := fun t ↦ localTensor ρ q F c.right.unop
                (((sheafPushforwardAbelian q).obj
                  ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)).obj.map
                  (CharacterSections.chartToBase q V.unop c).op t)
              map_zero' := sorry
              map_add' := sorry })
          (by
            intro R c d a b h
            ext t
            exact localTensor_compatible ρ q F V.unop a b h t)
      naturality := sorry }

include finiteG in
/-- On each actual torsor chart, the forward map is the finite sum of component tensors. -/
theorem projectionFormulaIntegerHom_chart (ρ : G →* Aut W) (q : W ⟶ U)
    [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (V : smallEtaleSite U)
    (c : CharacterSections.Charts q V)
    (t : ((sheafPushforwardAbelian q).obj
      ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)).obj.obj (op V)) :
    (tensorPushforwardConstantInteger q F).obj.map
        (CharacterSections.chartToBase q V c).op
        ((projectionFormulaIntegerHom ρ q F).hom.app (op V) t) =
      localTensor ρ q F c.right.unop
        (((sheafPushforwardAbelian q).obj
          ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)).obj.map
          (CharacterSections.chartToBase q V c).op t) := sorry

include finiteG in
/-- Projection formula for the finite torsor, with its actual glued finite-basis
map and chartwise multiplication as the two data legs. -/
noncomputable def projectionFormulaInteger
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (sheafPushforwardAbelian q).obj
        ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) ≅
      tensorPushforwardConstantInteger q F where
  hom := projectionFormulaIntegerHom ρ q F
  inv := projectionFormulaIntegerInv q F
  hom_inv_id := sorry
  inv_hom_id := sorry

include finiteG in
/-- The inverse leg is exactly the specified chart multiplication. -/
theorem projectionFormulaInteger_inv
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (projectionFormulaInteger ρ q F).inv = projectionFormulaIntegerInv q F := rfl

include finiteG in
/-- The forward leg is exactly the specified glued finite-basis map. -/
theorem projectionFormulaInteger_hom
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (projectionFormulaInteger ρ q F).hom = projectionFormulaIntegerHom ρ q F := rfl

include finiteG in
/-- Invertibility of chart multiplication follows from its constructed inverse. -/
theorem projectionFormulaIntegerInv_isIso
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    IsIso (projectionFormulaIntegerInv q F) :=
  (projectionFormulaInteger ρ q F).isIso_inv

/-- The G-equivariant identification `H^0(W, F|_W) ⟶ H^0(U, F ⊗_ℤ q_* ℤ̲)`. -/
noncomputable def globalSectionsProjectionFormulaHom
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (globalSections W).obj ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) ⟶
      (globalSections U).obj (tensorPushforwardConstantInteger q F) :=
  globalSectionsPushforwardHom q
      ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) ≫
    (globalSections U).map (projectionFormulaInteger ρ q F).hom

/-- The G-equivariant identification `H^0(U, F ⊗_ℤ q_* ℤ̲) ⟶ H^0(W, F|_W)`. -/
noncomputable def globalSectionsProjectionFormulaInv
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) :
    (globalSections U).obj (tensorPushforwardConstantInteger q F) ⟶
      (globalSections W).obj ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F) :=
  (globalSections U).map (projectionFormulaInteger ρ q F).inv ≫
    globalSectionsPushforwardInv q
      ((etaleRestrictionSheaf q AddCommGrpCat.{u + 1}).obj F)

/-- Projection-formula comparison of global sections is G-equivariant. -/
theorem globalSectionsProjectionFormulaHom_equivariant
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (g : G) :
    (globalSectionsAction ρ q F g).hom ≫
        globalSectionsProjectionFormulaHom ρ q F =
      globalSectionsProjectionFormulaHom ρ q F ≫
        (tensorPushforwardGlobalSectionsAction ρ q F g).hom := sorry

/-- Reverse projection-formula comparison of global sections is G-equivariant. -/
theorem globalSectionsProjectionFormulaInv_equivariant
    (ρ : G →* Aut W) (q : W ⟶ U) [IsFree ρ] [IsFreeQuotient ρ q]
    (F : Sheaf (smallEtaleTopology U) AddCommGrpCat.{u + 1}) (g : G) :
    (tensorPushforwardGlobalSectionsAction ρ q F g).hom ≫
        globalSectionsProjectionFormulaInv ρ q F =
      globalSectionsProjectionFormulaInv ρ q F ≫
        (globalSectionsAction ρ q F g).hom := sorry


end AlgebraicGeometry.AlgebraicSpace
