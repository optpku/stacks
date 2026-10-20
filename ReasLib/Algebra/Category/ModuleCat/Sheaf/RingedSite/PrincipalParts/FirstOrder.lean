module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts.FirstOrder
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.Construction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal

/-!
# The first principal-parts sequence on a ringed site

The topology-independent sequence is constructed in the presheaf owner.  This file sheafifies
that presentation and, when the canonical monoidal comparison is available, transports its left
term to the ambient tensor product `Ω(phi) ⊗ F`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.PrincipalParts.FirstOrder

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}

namespace Presentation

/-- The cotangent tensor presheaf whose sheafification presents the left term of the first
principal-parts sequence. -/
noncomputable abbrev cotangentPresheaf (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    PresheafOfModules (ringSheaf J O₂).obj :=
  PresheafOfModules.PrincipalParts.FirstOrder.cotangent phi.hom F.val

/-- The sheafification of the objectwise cotangent tensor presentation. -/
noncomputable abbrev cotangent (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) : ringedSiteModuleCategory J O₂ :=
  (moduleSheafification O₂).obj (cotangentPresheaf phi F)

/-- The sheafification of the objectwise cotangent arrow. -/
noncomputable abbrev cotangentTo (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    cotangent phi F ⟶ PrincipalParts.sheaf phi F 1 :=
  (moduleSheafification O₂).map
    (PresheafOfModules.PrincipalParts.FirstOrder.cotangentTo phi.hom F.val)

end Presentation

/-- The sheafification of the objectwise principal-parts projection, followed by the canonical
recovery isomorphism for the already existing module sheaf. -/
noncomputable def projection (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    PrincipalParts.sheaf phi F 1 ⟶ F :=
  (moduleSheafification O₂).map
      (PresheafOfModules.PrincipalParts.FirstOrder.projection phi.hom F.val) ≫
    (moduleSheafificationValIso O₂ F).hom

/-- Naturality of the sheafified principal-parts projection. -/
theorem projection_naturality (phi : O₁ ⟶ O₂)
    {F G : ringedSiteModuleCategory J O₂} (alpha : F ⟶ G) :
    PrincipalParts.map phi 1 alpha ≫ projection phi G = projection phi F ≫ alpha := sorry

namespace Presentation

/-- The two arrows of the sheafified presentation compose to zero. -/
theorem zero (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    cotangentTo phi F ≫ projection phi F = 0 := sorry

/-- The first principal-parts short complex in its sheafified cotangent presentation. -/
noncomputable def sequence (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    ShortComplex (ringedSiteModuleCategory J O₂) :=
  ShortComplex.mk (cotangentTo phi F) (projection phi F) (zero phi F)

section PresentationFunctoriality

variable {F G H : ringedSiteModuleCategory J O₂}

/-- The sheafified morphism on cotangent presentations induced by a module-sheaf morphism. -/
noncomputable abbrev cotangentMap (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    cotangent phi F ⟶ cotangent phi G :=
  (moduleSheafification O₂).map
    (PresheafOfModules.PrincipalParts.FirstOrder.cotangentMap phi.hom alpha.val)

/-- Naturality of the sheafified cotangent-presentation arrow. -/
theorem cotangentTo_naturality (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    cotangentMap phi alpha ≫ cotangentTo phi G =
      cotangentTo phi F ≫ PrincipalParts.map phi 1 alpha := sorry

/-- The morphism between sheafified-presentation sequences induced by a module-sheaf morphism. -/
noncomputable def sequenceMap (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    sequence phi F ⟶ sequence phi G :=
  ShortComplex.Hom.mk (cotangentMap phi alpha) (PrincipalParts.map phi 1 alpha) alpha
    (cotangentTo_naturality phi alpha) (projection_naturality phi alpha)

/-- Presentation-sequence functoriality preserves identity morphisms. -/
@[simp]
theorem sequenceMap_id (phi : O₁ ⟶ O₂) :
    sequenceMap phi (𝟙 F) = 𝟙 (sequence phi F) := sorry

/-- Presentation-sequence functoriality preserves composition. -/
@[simp]
theorem sequenceMap_comp (phi : O₁ ⟶ O₂)
    (alpha : F ⟶ G) (beta : G ⟶ H) :
    sequenceMap phi (alpha ≫ beta) = sequenceMap phi alpha ≫ sequenceMap phi beta := sorry

/-- The cotangent-presentation map preserves identity morphisms. -/
@[simp]
theorem cotangentMap_id (phi : O₁ ⟶ O₂) :
    cotangentMap phi (𝟙 F) = 𝟙 (cotangent phi F) := sorry

/-- The cotangent-presentation map preserves composition. -/
@[simp]
theorem cotangentMap_comp (phi : O₁ ⟶ O₂)
    (alpha : F ⟶ G) (beta : G ⟶ H) :
    cotangentMap phi (alpha ≫ beta) = cotangentMap phi alpha ≫ cotangentMap phi beta := sorry

/-- Sheafified cotangent presentations form a functor in the module sheaf. -/
noncomputable def cotangentFunctor (phi : O₁ ⟶ O₂) :
    ringedSiteModuleCategory J O₂ ⥤ ringedSiteModuleCategory J O₂ where
  obj F := cotangent phi F
  map alpha := cotangentMap phi alpha
  map_id F := cotangentMap_id phi
  map_comp alpha beta := cotangentMap_comp phi alpha beta

/-- The sheafified-presentation first-principal-parts sequence is functorial in the module
sheaf. -/
noncomputable def sequenceFunctor (phi : O₁ ⟶ O₂) :
    ringedSiteModuleCategory J O₂ ⥤ ShortComplex (ringedSiteModuleCategory J O₂) where
  obj F := sequence phi F
  map alpha := sequenceMap phi alpha
  map_id F := sequenceMap_id phi
  map_comp alpha beta := sequenceMap_comp phi alpha beta

end PresentationFunctoriality

/-- Under exact module sheafification, the sheafified-presentation first-principal-parts
sequence is short exact. -/
theorem shortExact [HasSheafify J AddCommGrpCat.{max u v}]
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    (sequence phi F).ShortExact := sorry

end Presentation

section CanonicalTensor

/-- The canonical cotangent tensor `Ω(phi) ⊗[O₂] F` in the ambient monoidal category of module
sheaves. -/
noncomputable abbrev cotangentTensor (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) : ringedSiteModuleCategory J O₂ :=
  moduleTensor (relativeDifferentials phi) F

/-- The monoidal sheafification comparison identifies the canonical cotangent tensor with its
objectwise presentation. -/
noncomputable def cotangentComparison (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    cotangentTensor phi F ≅ Presentation.cotangent phi F :=
  tensorIso (Iso.refl (relativeDifferentials phi))
      (moduleSheafificationValIso O₂ F).symm ≪≫
    ModuleSheafification.tensorIso O₂ (relativeDifferentials' phi.hom) F.val

/-- The canonical cotangent arrow in the first principal-parts sequence. -/
noncomputable def cotangentTo (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    cotangentTensor phi F ⟶ PrincipalParts.sheaf phi F 1 :=
  (cotangentComparison phi F).hom ≫ Presentation.cotangentTo phi F

/-- The canonical cotangent and projection arrows compose to zero. -/
theorem zero (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    cotangentTo phi F ≫ projection phi F = 0 := sorry

/-- The canonical first principal-parts short complex
`Ω(phi) ⊗[O₂] F ⟶ P¹(phi, F) ⟶ F`. -/
@[stacks 09CW "principal-parts sequence", stacks 0G3V "principal-parts sequence"]
noncomputable def sequence (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    ShortComplex (ringedSiteModuleCategory J O₂) :=
  ShortComplex.mk (cotangentTo phi F) (projection phi F) (zero phi F)

section Functoriality

variable {F G H : ringedSiteModuleCategory J O₂}

/-- The morphism on canonical cotangent tensors induced by a module-sheaf morphism. -/
noncomputable abbrev cotangentMap (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    cotangentTensor phi F ⟶ cotangentTensor phi G :=
  moduleTensorMap (𝟙 (relativeDifferentials phi)) alpha

/-- Cotangent tensor functoriality preserves identity morphisms. -/
@[simp]
theorem cotangentMap_id (phi : O₁ ⟶ O₂) :
    cotangentMap phi (𝟙 F) = 𝟙 (cotangentTensor phi F) := sorry

/-- Cotangent tensor functoriality preserves composition. -/
@[simp]
theorem cotangentMap_comp (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) (beta : G ⟶ H) :
    cotangentMap phi (alpha ≫ beta) = cotangentMap phi alpha ≫ cotangentMap phi beta := sorry

/-- Tensoring with `Ω(phi)` defines an endofunctor on module sheaves. -/
noncomputable def cotangentFunctor (phi : O₁ ⟶ O₂) :
    ringedSiteModuleCategory J O₂ ⥤ ringedSiteModuleCategory J O₂ where
  obj F := cotangentTensor phi F
  map alpha := cotangentMap phi alpha
  map_id F := cotangentMap_id phi
  map_comp alpha beta := cotangentMap_comp phi alpha beta

/-- The comparison from canonical cotangent tensors to their sheafified presentations is natural
in the module sheaf. -/
theorem cotangentComparison_naturality (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    cotangentMap phi alpha ≫ (cotangentComparison phi G).hom =
      (cotangentComparison phi F).hom ≫ Presentation.cotangentMap phi alpha := sorry

namespace CotangentComparison

/-- The inverse cotangent comparison is natural in the module sheaf. -/
@[stacks 09CW "inverse cotangent presentation comparison naturality",
  stacks 0G3V "inverse cotangent presentation comparison naturality"]
theorem inv_naturality (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    Presentation.cotangentMap phi alpha ≫ (cotangentComparison phi G).inv =
      (cotangentComparison phi F).inv ≫ cotangentMap phi alpha := sorry

/-- The forward cotangent comparisons form a natural transformation. -/
@[stacks 09CW "forward cotangent presentation comparison natural transformation",
  stacks 0G3V "forward cotangent presentation comparison natural transformation"]
noncomputable def natTrans (phi : O₁ ⟶ O₂) :
    cotangentFunctor phi ⟶ Presentation.cotangentFunctor phi where
  app F := (cotangentComparison phi F).hom
  naturality _ _ alpha := cotangentComparison_naturality phi alpha

/-- The inverse cotangent comparisons form the inverse natural transformation. -/
@[stacks 09CW "inverse cotangent presentation comparison natural transformation",
  stacks 0G3V "inverse cotangent presentation comparison natural transformation"]
noncomputable def invNatTrans (phi : O₁ ⟶ O₂) :
    Presentation.cotangentFunctor phi ⟶ cotangentFunctor phi where
  app F := (cotangentComparison phi F).inv
  naturality _ _ alpha := inv_naturality phi alpha

/-- A component of the forward cotangent comparison is the objectwise forward map. -/
@[simp, stacks 09CW "forward cotangent presentation comparison component",
  stacks 0G3V "forward cotangent presentation comparison component"]
theorem natTrans_app (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    (natTrans phi).app F = (cotangentComparison phi F).hom := sorry

/-- A component of the inverse cotangent comparison is the objectwise inverse map. -/
@[simp, stacks 09CW "inverse cotangent presentation comparison component",
  stacks 0G3V "inverse cotangent presentation comparison component"]
theorem invNatTrans_app (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    (invNatTrans phi).app F = (cotangentComparison phi F).inv := sorry

/-- The forward cotangent comparison followed by its inverse is the identity. -/
@[simp, stacks 09CW "cotangent presentation comparison forward-inverse law",
  stacks 0G3V "cotangent presentation comparison forward-inverse law"]
theorem hom_inv_id (phi : O₁ ⟶ O₂) :
    natTrans phi ≫ invNatTrans phi = 𝟙 _ := sorry

/-- The inverse cotangent comparison followed by its forward map is the identity. -/
@[simp, stacks 09CW "cotangent presentation comparison inverse-forward law",
  stacks 0G3V "cotangent presentation comparison inverse-forward law"]
theorem inv_hom_id (phi : O₁ ⟶ O₂) :
    invNatTrans phi ≫ natTrans phi = 𝟙 _ := sorry

end CotangentComparison

/-- The canonical cotangent-tensor functor is naturally isomorphic to the sheafified
presentation functor. -/
@[stacks 09CW "cotangent presentation comparison",
  stacks 0G3V "cotangent presentation comparison"]
noncomputable def cotangentComparisonNatIso (phi : O₁ ⟶ O₂) :
    cotangentFunctor phi ≅ Presentation.cotangentFunctor phi :=
  { hom := CotangentComparison.natTrans phi
    inv := CotangentComparison.invNatTrans phi
    hom_inv_id := CotangentComparison.hom_inv_id phi
    inv_hom_id := CotangentComparison.inv_hom_id phi }

/-- The forward natural transformation of `cotangentComparisonNatIso` is explicit. -/
@[simp, stacks 09CW "cotangent presentation comparison natural isomorphism hom",
  stacks 0G3V "cotangent presentation comparison natural isomorphism hom"]
theorem cotangentComparisonNatIso_hom (phi : O₁ ⟶ O₂) :
    (cotangentComparisonNatIso phi).hom = CotangentComparison.natTrans phi := sorry

/-- The inverse natural transformation of `cotangentComparisonNatIso` is explicit. -/
@[simp, stacks 09CW "cotangent presentation comparison natural isomorphism inverse",
  stacks 0G3V "cotangent presentation comparison natural isomorphism inverse"]
theorem cotangentComparisonNatIso_inv (phi : O₁ ⟶ O₂) :
    (cotangentComparisonNatIso phi).inv = CotangentComparison.invNatTrans phi := sorry

/-- The component of the cotangent comparison natural isomorphism is the canonical objectwise
comparison. -/
@[simp]
theorem cotangentComparisonNatIso_app (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    (cotangentComparisonNatIso phi).app F = cotangentComparison phi F := sorry

/-- The forward component of the cotangent comparison natural isomorphism is the forward
objectwise comparison. -/
@[simp]
theorem cotangentComparisonNatIso_hom_app (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    (cotangentComparisonNatIso phi).hom.app F = (cotangentComparison phi F).hom := sorry

/-- The inverse component of the cotangent comparison natural isomorphism is the inverse
objectwise comparison. -/
@[simp]
theorem cotangentComparisonNatIso_inv_app (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    (cotangentComparisonNatIso phi).inv.app F = (cotangentComparison phi F).inv := sorry

/-- Naturality of the canonical cotangent arrow. -/
theorem cotangentTo_naturality (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    cotangentMap phi alpha ≫ cotangentTo phi G =
      cotangentTo phi F ≫ PrincipalParts.map phi 1 alpha := sorry

/-- The canonical cotangent arrows form a natural transformation into first principal parts. -/
noncomputable def cotangentToNatTrans (phi : O₁ ⟶ O₂) :
    cotangentFunctor phi ⟶ PrincipalParts.functor phi 1 where
  app F := cotangentTo phi F
  naturality F G alpha := cotangentTo_naturality phi alpha

/-- The first-principal-parts projections form a natural transformation to the identity
functor. -/
noncomputable def projectionNatTrans (phi : O₁ ⟶ O₂) :
    PrincipalParts.functor phi 1 ⟶ 𝟭 (ringedSiteModuleCategory J O₂) where
  app F := projection phi F
  naturality F G alpha := projection_naturality phi alpha

/-- The functorial morphism of canonical first-principal-parts short complexes. -/
noncomputable def sequenceMap (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    sequence phi F ⟶ sequence phi G :=
  ShortComplex.Hom.mk (cotangentMap phi alpha) (PrincipalParts.map phi 1 alpha) alpha
    (cotangentTo_naturality phi alpha) (projection_naturality phi alpha)

/-- Canonical sequence functoriality preserves identity morphisms. -/
@[simp]
theorem sequenceMap_id (phi : O₁ ⟶ O₂) :
    sequenceMap phi (𝟙 F) = 𝟙 (sequence phi F) := sorry

/-- Canonical sequence functoriality preserves composition. -/
@[simp]
theorem sequenceMap_comp (phi : O₁ ⟶ O₂)
    (alpha : F ⟶ G) (beta : G ⟶ H) :
    sequenceMap phi (alpha ≫ beta) = sequenceMap phi alpha ≫ sequenceMap phi beta := sorry

/-- The canonical first-principal-parts sequence is functorial in the module sheaf. -/
noncomputable def sequenceFunctor (phi : O₁ ⟶ O₂) :
    ringedSiteModuleCategory J O₂ ⥤ ShortComplex (ringedSiteModuleCategory J O₂) where
  obj F := sequence phi F
  map alpha := sequenceMap phi alpha
  map_id F := sequenceMap_id phi
  map_comp alpha beta := sequenceMap_comp phi alpha beta

/-- The cotangent comparison intertwines the left arrows of the canonical and presentation
first-principal-parts sequences. -/
theorem sequenceIso_comm₁₂ (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    (cotangentComparison phi F).hom ≫ (Presentation.sequence phi F).f =
      (sequence phi F).f ≫ (Iso.refl (PrincipalParts.sheaf phi F 1)).hom := sorry

/-- The identity comparisons on the middle and right terms intertwine the projection arrows of
the canonical and presentation first-principal-parts sequences. -/
theorem sequenceIso_comm₂₃ (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    (Iso.refl (PrincipalParts.sheaf phi F 1)).hom ≫
        (Presentation.sequence phi F).g =
      (sequence phi F).g ≫ (Iso.refl F).hom := sorry

/-- The canonical and sheafified-presentation first-principal-parts sequences are isomorphic;
only their cotangent terms require a nonidentity comparison. -/
@[stacks 09CW "presentation sequence comparison",
  stacks 0G3V "presentation sequence comparison"]
noncomputable def sequenceIso (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    sequence phi F ≅ Presentation.sequence phi F :=
  ShortComplex.isoMk (cotangentComparison phi F)
    (Iso.refl (PrincipalParts.sheaf phi F 1)) (Iso.refl F)
    (sequenceIso_comm₁₂ phi F) (sequenceIso_comm₂₃ phi F)

/-- The forward comparison of first-principal-parts sequences has the canonical cotangent
comparison as its left component. -/
@[simp]
theorem sequenceIso_hom_τ₁ (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    (sequenceIso phi F).hom.τ₁ = (cotangentComparison phi F).hom := sorry

/-- The forward comparison of first-principal-parts sequences is the identity on the middle
principal-parts sheaf. -/
@[simp]
theorem sequenceIso_hom_τ₂ (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    (sequenceIso phi F).hom.τ₂ = 𝟙 (PrincipalParts.sheaf phi F 1) := sorry

/-- The forward comparison of first-principal-parts sequences is the identity on the original
module sheaf. -/
@[simp]
theorem sequenceIso_hom_τ₃ (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    (sequenceIso phi F).hom.τ₃ = 𝟙 F := sorry

/-- The inverse comparison of first-principal-parts sequences has the inverse cotangent
comparison as its left component. -/
@[simp]
theorem sequenceIso_inv_τ₁ (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    (sequenceIso phi F).inv.τ₁ = (cotangentComparison phi F).inv := sorry

/-- The inverse comparison of first-principal-parts sequences is the identity on the middle
principal-parts sheaf. -/
@[simp]
theorem sequenceIso_inv_τ₂ (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    (sequenceIso phi F).inv.τ₂ = 𝟙 (PrincipalParts.sheaf phi F 1) := sorry

/-- The inverse comparison of first-principal-parts sequences is the identity on the original
module sheaf. -/
@[simp]
theorem sequenceIso_inv_τ₃ (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    (sequenceIso phi F).inv.τ₃ = 𝟙 F := sorry

/-- The objectwise sequence comparisons are natural in the module sheaf. -/
theorem sequenceIso_naturality (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    sequenceMap phi alpha ≫ (sequenceIso phi G).hom =
      (sequenceIso phi F).hom ≫ Presentation.sequenceMap phi alpha := sorry

namespace SequenceComparison

/-- The inverse presentation-sequence comparison is natural in the module sheaf. -/
@[stacks 09CW "inverse presentation sequence comparison naturality",
  stacks 0G3V "inverse presentation sequence comparison naturality"]
theorem inv_naturality (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    Presentation.sequenceMap phi alpha ≫ (sequenceIso phi G).inv =
      (sequenceIso phi F).inv ≫ sequenceMap phi alpha := sorry

/-- The forward presentation-sequence comparisons form a natural transformation. -/
@[stacks 09CW "forward presentation sequence comparison natural transformation",
  stacks 0G3V "forward presentation sequence comparison natural transformation"]
noncomputable def natTrans (phi : O₁ ⟶ O₂) :
    sequenceFunctor phi ⟶ Presentation.sequenceFunctor phi where
  app F := (sequenceIso phi F).hom
  naturality _ _ alpha := sequenceIso_naturality phi alpha

/-- The inverse presentation-sequence comparisons form the inverse natural transformation. -/
@[stacks 09CW "inverse presentation sequence comparison natural transformation",
  stacks 0G3V "inverse presentation sequence comparison natural transformation"]
noncomputable def invNatTrans (phi : O₁ ⟶ O₂) :
    Presentation.sequenceFunctor phi ⟶ sequenceFunctor phi where
  app F := (sequenceIso phi F).inv
  naturality _ _ alpha := inv_naturality phi alpha

/-- A component of the forward presentation-sequence comparison is the objectwise forward map. -/
@[simp, stacks 09CW "forward presentation sequence comparison component",
  stacks 0G3V "forward presentation sequence comparison component"]
theorem natTrans_app (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    (natTrans phi).app F = (sequenceIso phi F).hom := sorry

/-- A component of the inverse presentation-sequence comparison is the objectwise inverse map. -/
@[simp, stacks 09CW "inverse presentation sequence comparison component",
  stacks 0G3V "inverse presentation sequence comparison component"]
theorem invNatTrans_app (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    (invNatTrans phi).app F = (sequenceIso phi F).inv := sorry

/-- The forward presentation-sequence comparison followed by its inverse is the identity. -/
@[simp, stacks 09CW "presentation sequence comparison forward-inverse law",
  stacks 0G3V "presentation sequence comparison forward-inverse law"]
theorem hom_inv_id (phi : O₁ ⟶ O₂) :
    natTrans phi ≫ invNatTrans phi = 𝟙 _ := sorry

/-- The inverse presentation-sequence comparison followed by its forward map is the identity. -/
@[simp, stacks 09CW "presentation sequence comparison inverse-forward law",
  stacks 0G3V "presentation sequence comparison inverse-forward law"]
theorem inv_hom_id (phi : O₁ ⟶ O₂) :
    invNatTrans phi ≫ natTrans phi = 𝟙 _ := sorry

end SequenceComparison

/-- The canonical first-principal-parts sequence functor is naturally isomorphic to its
sheafified-presentation model. -/
@[stacks 09CW "natural presentation sequence comparison",
  stacks 0G3V "natural presentation sequence comparison"]
noncomputable def sequenceNatIso (phi : O₁ ⟶ O₂) :
    sequenceFunctor phi ≅ Presentation.sequenceFunctor phi :=
  { hom := SequenceComparison.natTrans phi
    inv := SequenceComparison.invNatTrans phi
    hom_inv_id := SequenceComparison.hom_inv_id phi
    inv_hom_id := SequenceComparison.inv_hom_id phi }

/-- The forward natural transformation of `sequenceNatIso` is explicit. -/
@[simp, stacks 09CW "presentation sequence comparison natural isomorphism hom",
  stacks 0G3V "presentation sequence comparison natural isomorphism hom"]
theorem sequenceNatIso_hom (phi : O₁ ⟶ O₂) :
    (sequenceNatIso phi).hom = SequenceComparison.natTrans phi := sorry

/-- The inverse natural transformation of `sequenceNatIso` is explicit. -/
@[simp, stacks 09CW "presentation sequence comparison natural isomorphism inverse",
  stacks 0G3V "presentation sequence comparison natural isomorphism inverse"]
theorem sequenceNatIso_inv (phi : O₁ ⟶ O₂) :
    (sequenceNatIso phi).inv = SequenceComparison.invNatTrans phi := sorry

/-- The component of the natural sequence comparison is the objectwise sequence isomorphism. -/
@[simp]
theorem sequenceNatIso_app (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    (sequenceNatIso phi).app F = sequenceIso phi F := sorry

/-- The forward component of the natural sequence comparison is the forward objectwise
comparison. -/
@[simp]
theorem sequenceNatIso_hom_app (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    (sequenceNatIso phi).hom.app F = (sequenceIso phi F).hom := sorry

/-- The inverse component of the natural sequence comparison is the inverse objectwise
comparison. -/
@[simp]
theorem sequenceNatIso_inv_app (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) :
    (sequenceNatIso phi).inv.app F = (sequenceIso phi F).inv := sorry

end Functoriality

/-- The left object of the canonical first-principal-parts sequence is `Ω(phi) ⊗[O₂] F`. -/
@[simp]
theorem sequence_X₁ (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    (sequence phi F).X₁ = cotangentTensor phi F := sorry

/-- The middle object of the canonical first-principal-parts sequence is the first
principal-parts sheaf. -/
@[simp]
theorem sequence_X₂ (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    (sequence phi F).X₂ = PrincipalParts.sheaf phi F 1 := sorry

/-- The right object of the canonical first-principal-parts sequence is the original module
sheaf. -/
@[simp]
theorem sequence_X₃ (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    (sequence phi F).X₃ = F := sorry

/-- The canonical functorial first-principal-parts sequence is short
exact. -/
@[stacks 09CW "short exact", stacks 0G3V "short exact"]
theorem shortExact [HasSheafify J AddCommGrpCat.{max u v}]
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    (sequence phi F).ShortExact := sorry

end CanonicalTensor

end SheafOfModules.RingedSite.PrincipalParts.FirstOrder
