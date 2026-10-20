module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quotients by ideal sheaves on a ringed site

The quotient of a ring sheaf by an ideal sheaf is obtained by sheafifying the presheaf of
sectionwise quotients.  The section objects, restriction maps, projections, and change-of-rings
maps are explicit data; functoriality and naturality are isolated as named proof obligations.
Quotients by ideal powers carry maps for every inequality of exponents, hence canonical inverse
systems of presheaves and sheaves, whose successive kernels own the associated graded pieces.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O O' : Sheaf J CommRingCat.{w}}

namespace IdealPower

/-- Some uniform power of the ideal sheaf `I` annihilates every section of `F`. -/
@[stacks 0GLY "annihilation condition"]
def IsAnnihilated
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory J O) : Prop :=
  ∃ n : ℕ, ∀ U : Cᵒᵖ,
    IdealSheaf.sections I U ^ n ≤
      Module.annihilator (O.obj.obj U) (F.val.obj U)

/-- Unfolding the uniform ideal-power annihilation predicate. -/
theorem isAnnihilated_iff
    (I : Subobject (unitModule J O))
    (F : ringedSiteModuleCategory J O) :
    IsAnnihilated I F ↔
      ∃ n : ℕ, ∀ U : Cᵒᵖ,
        IdealSheaf.sections I U ^ n ≤
          Module.annihilator (O.obj.obj U) (F.val.obj U) := sorry

end IdealPower

namespace IdealSheaf.Quotient

/-- The section object of the quotient presheaf `O / I`. -/
noncomputable abbrev sections
    (I : Subobject (unitModule J O)) (U : Cᵒᵖ) : CommRingCat.{w} :=
  CommRingCat.of (O.obj.obj U ⧸ IdealSheaf.sections I U)

/-- The restriction map on the sectionwise quotient presheaf `O / I`. -/
noncomputable def restriction
    (I : Subobject (unitModule J O)) {U V : Cᵒᵖ} (f : U ⟶ V) :
    sections I U ⟶ sections I V :=
  CommRingCat.ofHom <|
    Ideal.quotientMap (IdealSheaf.sections I V) (O.obj.map f).hom
      (IdealSheaf.sections_le_comap I f)

/-- Identity restrictions act identically on sectionwise quotients. -/
theorem restriction_id
    (I : Subobject (unitModule J O)) (U : Cᵒᵖ) :
    restriction I (𝟙 U) = 𝟙 (sections I U) := sorry

/-- Composite restrictions act by the composite map on sectionwise quotients. -/
theorem restriction_comp
    (I : Subobject (unitModule J O)) {U V W : Cᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    restriction I (f ≫ g) =
      restriction I f ≫ restriction I g := sorry

/-- The presheaf of commutative rings whose sections are `O(U) / I(U)`. -/
noncomputable def presheaf
    (I : Subobject (unitModule J O)) : Cᵒᵖ ⥤ CommRingCat.{w} where
  obj U := sections I U
  map f := restriction I f
  map_id U := restriction_id I U
  map_comp f g := restriction_comp I f g

/-- The quotient projection on one object of the site. -/
noncomputable def sectionProjection
    (I : Subobject (unitModule J O)) (U : Cᵒᵖ) :
    O.obj.obj U ⟶ sections I U :=
  CommRingCat.ofHom (Ideal.Quotient.mk _)

/-- The sectionwise quotient projections commute with restrictions. -/
theorem sectionProjection_naturality
    (I : Subobject (unitModule J O)) {U V : Cᵒᵖ} (f : U ⟶ V) :
    O.obj.map f ≫ sectionProjection I V =
      sectionProjection I U ≫ restriction I f := sorry

/-- The presheaf-level quotient projection `O ⟶ O / I`. -/
noncomputable def presheafProjection
    (I : Subobject (unitModule J O)) : O.obj ⟶ presheaf I where
  app U := sectionProjection I U
  naturality {_ _} f := sectionProjection_naturality I f

/-- A section of `I` maps to zero under a sheaf map whose kernel contains `I`. -/
theorem map_eq_zero_of_mem
    (I : Subobject (unitModule J O)) (alpha : O ⟶ O')
    (hI : I ≤ KernelIdeal.subobject alpha) (U : Cᵒᵖ)
    {x : O.obj.obj U} (hx : x ∈ IdealSheaf.sections I U) :
    alpha.hom.app U x = 0 := sorry

/-- The sectionwise map out of `O(U) / I(U)` induced by a sheaf map annihilating `I`. -/
noncomputable def sectionLift
    (I : Subobject (unitModule J O)) (alpha : O ⟶ O')
    (hI : I ≤ KernelIdeal.subobject alpha) (U : Cᵒᵖ) :
    sections I U ⟶ O'.obj.obj U :=
  CommRingCat.ofHom <|
    Ideal.Quotient.lift (IdealSheaf.sections I U) (alpha.hom.app U).hom
      (fun x hx => map_eq_zero_of_mem I alpha hI U hx)

/-- The sectionwise quotient projection followed by its induced lift is the original map. -/
@[reassoc]
theorem sectionProjection_comp_sectionLift
    (I : Subobject (unitModule J O)) (alpha : O ⟶ O')
    (hI : I ≤ KernelIdeal.subobject alpha) (U : Cᵒᵖ) :
    sectionProjection I U ≫ sectionLift I alpha hI U =
      alpha.hom.app U := sorry

/-- The sectionwise quotient lifts commute with restriction maps. -/
theorem sectionLift_naturality
    (I : Subobject (unitModule J O)) (alpha : O ⟶ O')
    (hI : I ≤ KernelIdeal.subobject alpha)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    restriction I f ≫ sectionLift I alpha hI V =
      sectionLift I alpha hI U ≫ O'.obj.map f := sorry

/-- The presheaf map out of `O / I` induced by a sheaf map annihilating `I`. -/
noncomputable def presheafLift
    (I : Subobject (unitModule J O)) (alpha : O ⟶ O')
    (hI : I ≤ KernelIdeal.subobject alpha) :
    presheaf I ⟶ O'.obj where
  app U := sectionLift I alpha hI U
  naturality {_ _} f := sectionLift_naturality I alpha hI f

/-- The presheaf quotient projection followed by its induced lift is the original map. -/
@[reassoc]
theorem presheafProjection_comp_lift
    (I : Subobject (unitModule J O)) (alpha : O ⟶ O')
    (hI : I ≤ KernelIdeal.subobject alpha) :
    presheafProjection I ≫ presheafLift I alpha hI = alpha.hom := sorry

section QuotientSheaf

variable [HasWeakSheafify J CommRingCat.{w}]

/-- The quotient sheaf of commutative rings `O / I`. -/
@[stacks 0GLY "quotient sheaf"]
noncomputable abbrev sheaf
    (I : Subobject (unitModule J O)) : Sheaf J CommRingCat.{w} :=
  PresheafOfModules.commRingSheafification J (presheaf I)

/-- The canonical quotient projection `O ⟶ O / I`. -/
noncomputable def projection
    (I : Subobject (unitModule J O)) : O ⟶ sheaf I :=
  { hom := presheafProjection I ≫
      CategoryTheory.toSheafify J (presheaf I) }

/-- The sheaf map out of `O / I` induced by a sheaf map annihilating `I`. Its data is the
sectionwise quotient eliminator followed by the sheafification universal map. -/
@[stacks 01HP "ideal-sheaf quotient eliminator"]
noncomputable def lift
    (I : Subobject (unitModule J O)) (alpha : O ⟶ O')
    (hI : I ≤ KernelIdeal.subobject alpha) :
    sheaf I ⟶ O' :=
  { hom := CategoryTheory.sheafifyLift J
      (presheafLift I alpha hI) O'.property }

/-- The quotient projection followed by the induced sheaf lift is the original map. -/
@[reassoc, simp]
theorem projection_comp_lift
    (I : Subobject (unitModule J O)) (alpha : O ⟶ O')
    (hI : I ≤ KernelIdeal.subobject alpha) :
    projection I ≫ lift I alpha hI = alpha := sorry

/-- A map out of the quotient sheaf is determined by its composite with the quotient
projection. -/
theorem lift_unique
    (I : Subobject (unitModule J O)) (alpha : O ⟶ O')
    (hI : I ≤ KernelIdeal.subobject alpha) (beta : sheaf I ⟶ O')
    (hbeta : projection I ≫ beta = alpha) :
    beta = lift I alpha hI := sorry

/-- The quotient projection of a sheaf of rings by an ideal sheaf is locally surjective. -/
@[stacks 0H2K "locally surjective quotient projection"]
instance projection_isLocallySurjective
    (I : Subobject (unitModule J O)) :
    Sheaf.IsLocallySurjective (projection I) := sorry

/-- The kernel ideal of the quotient projection is the original ideal subobject. -/
@[simp, stacks 0H2K "kernel of the quotient projection"]
theorem kernelIdealSubobject_projection
    (I : Subobject (unitModule J O)) :
    KernelIdeal.subobject (projection I) = I := sorry

/-- The quotient ring sheaf `O / I`, after forgetting commutativity. -/
noncomputable abbrev ringSheaf
    (I : Subobject (unitModule J O)) : Sheaf J RingCat.{w} :=
  SheafOfModules.RingedSite.ringSheaf J (sheaf I)

/-- The quotient projection after forgetting commutativity. -/
noncomputable abbrev ringProjection
    (I : Subobject (unitModule J O)) :
    SheafOfModules.RingedSite.ringSheaf J O ⟶ ringSheaf I :=
  SheafOfModules.RingedSite.ringSheafMap (projection I)

end QuotientSheaf

end IdealSheaf.Quotient

namespace IdealSheaf.PowerQuotient

/-- Restriction maps preserve every sectionwise ideal power. -/
theorem sections_le_comap
    (I : Subobject (unitModule J O)) {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℕ) :
    IdealSheaf.sections I U ^ n ≤
      (IdealSheaf.sections I V ^ n).comap (O.obj.map f).hom := sorry

/-- The section object of the quotient presheaf `O / I ^ n`. -/
noncomputable abbrev sections
    (I : Subobject (unitModule J O)) (n : ℕ) (U : Cᵒᵖ) : CommRingCat.{w} :=
  CommRingCat.of (O.obj.obj U ⧸ IdealSheaf.sections I U ^ n)

/-- The restriction map on the sectionwise quotient presheaf `O / I ^ n`. -/
noncomputable def restriction
    (I : Subobject (unitModule J O)) (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V) :
    sections I n U ⟶ sections I n V :=
  CommRingCat.ofHom <|
    Ideal.quotientMap (IdealSheaf.sections I V ^ n) (O.obj.map f).hom
      (sections_le_comap I f n)

/-- Identity restrictions act identically on quotients by an ideal power. -/
theorem restriction_id
    (I : Subobject (unitModule J O)) (n : ℕ) (U : Cᵒᵖ) :
    restriction I n (𝟙 U) =
      𝟙 (sections I n U) := sorry

/-- Composite restrictions act by the composite map on quotients by an ideal power. -/
theorem restriction_comp
    (I : Subobject (unitModule J O)) (n : ℕ) {U V W : Cᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    restriction I n (f ≫ g) =
      restriction I n f ≫
        restriction I n g := sorry

/-- The presheaf of sectionwise quotients `O(U) / I(U) ^ n`. -/
noncomputable def presheaf
    (I : Subobject (unitModule J O)) (n : ℕ) : Cᵒᵖ ⥤ CommRingCat.{w} where
  obj U := sections I n U
  map f := restriction I n f
  map_id U := restriction_id I n U
  map_comp f g := restriction_comp I n f g

/-- The quotient-by-`I ^ n` projection on one object of the site. -/
noncomputable def sectionProjection
    (I : Subobject (unitModule J O)) (n : ℕ) (U : Cᵒᵖ) :
    O.obj.obj U ⟶ sections I n U :=
  CommRingCat.ofHom (Ideal.Quotient.mk _)

/-- The quotient-by-`I ^ n` projections commute with restrictions. -/
theorem sectionProjection_naturality
    (I : Subobject (unitModule J O)) (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V) :
    O.obj.map f ≫ sectionProjection I n V =
      sectionProjection I n U ≫
        restriction I n f := sorry

/-- The presheaf-level quotient projection `O ⟶ O / I ^ n`. -/
noncomputable def presheafProjection
    (I : Subobject (unitModule J O)) (n : ℕ) :
    O.obj ⟶ presheaf I n where
  app U := sectionProjection I n U
  naturality {_ _} f :=
    sectionProjection_naturality I n f

section Sheafification

variable [HasWeakSheafify J CommRingCat.{w}]

/-- The quotient sheaf of commutative rings `O / I ^ n`. -/
noncomputable abbrev sheaf
    (I : Subobject (unitModule J O)) (n : ℕ) : Sheaf J CommRingCat.{w} :=
  PresheafOfModules.commRingSheafification J (presheaf I n)

/-- The canonical quotient projection `O ⟶ O / I ^ n`. -/
noncomputable def projection
    (I : Subobject (unitModule J O)) (n : ℕ) :
    O ⟶ sheaf I n :=
  { hom := presheafProjection I n ≫
      CategoryTheory.toSheafify J (presheaf I n) }

/-- The quotient ring sheaf `O / I ^ n`, after forgetting commutativity. -/
noncomputable abbrev ringSheaf
    (I : Subobject (unitModule J O)) (n : ℕ) : Sheaf J RingCat.{w} :=
  SheafOfModules.RingedSite.ringSheaf J (sheaf I n)

/-- The projection `O ⟶ O / I ^ n` after forgetting commutativity. -/
noncomputable abbrev ringProjection
    (I : Subobject (unitModule J O)) (n : ℕ) :
    SheafOfModules.RingedSite.ringSheaf J O ⟶ ringSheaf I n :=
  SheafOfModules.RingedSite.ringSheafMap (projection I n)

end Sheafification

/-- The canonical section map `O(U) / I(U) ^ m ⟶ O(U) / I(U) ^ n` associated to an
inequality `n ≤ m`. -/
noncomputable def sectionMap
    (I : Subobject (unitModule J O)) {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) :
    sections I m U ⟶ sections I n U :=
  CommRingCat.ofHom (Ideal.Quotient.factorPow (IdealSheaf.sections I U) h)

/-- The maps between sectionwise ideal-power quotients commute with restriction maps. -/
theorem sectionMap_naturality
    (I : Subobject (unitModule J O)) {m n : ℕ} (h : n ≤ m)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    restriction I m f ≫ sectionMap I h V =
      sectionMap I h U ≫ restriction I n f := sorry

/-- The presheaf map `O / I ^ m ⟶ O / I ^ n` associated to `n ≤ m`. -/
noncomputable def presheafMap
    (I : Subobject (unitModule J O)) {m n : ℕ} (h : n ≤ m) :
    presheaf I m ⟶
      presheaf I n where
  app U := sectionMap I h U
  naturality {_ _} f := sectionMap_naturality I h f

/-- The quotient projection to `O / I ^ m`, followed by the presheaf map associated to
`n ≤ m`, is the quotient projection to `O / I ^ n`. -/
theorem presheafProjection_comp_map
    (I : Subobject (unitModule J O)) {m n : ℕ} (h : n ≤ m) :
    presheafProjection I m ≫ presheafMap I h =
      presheafProjection I n := sorry

/-- The one-step section map `O(U) / I(U) ^ (n + 1) ⟶ O(U) / I(U) ^ n`. -/
noncomputable abbrev sectionTransition
    (I : Subobject (unitModule J O)) (n : ℕ) (U : Cᵒᵖ) :
    sections I (n + 1) U ⟶ sections I n U :=
  sectionMap I n.le_succ U

/-- The one-step presheaf transition `O / I ^ (n + 1) ⟶ O / I ^ n`. -/
noncomputable abbrev presheafTransition
    (I : Subobject (unitModule J O)) (n : ℕ) :
    presheaf I (n + 1) ⟶
      presheaf I n :=
  presheafMap I n.le_succ

/-- The inverse system of presheaves `n ↦ O / I ^ n`. -/
noncomputable abbrev presheafSystem
    (I : Subobject (unitModule J O)) :
    ℕᵒᵖ ⥤ (Cᵒᵖ ⥤ CommRingCat.{w}) :=
  Functor.ofOpSequence (presheafTransition I)

section Sheaf

variable [HasWeakSheafify J CommRingCat.{w}]

/-- The sheaf map `O / I ^ m ⟶ O / I ^ n` associated to `n ≤ m`. -/
noncomputable abbrev sheafMap
    (I : Subobject (unitModule J O)) {m n : ℕ} (h : n ≤ m) :
    sheaf I m ⟶
      sheaf I n :=
  PresheafOfModules.commRingSheafificationMap J (presheafMap I h)

/-- The quotient projection to `O / I ^ m`, followed by the sheaf map associated to
`n ≤ m`, is the quotient projection to `O / I ^ n`. -/
theorem sheafProjection_comp_map
    (I : Subobject (unitModule J O)) {m n : ℕ} (h : n ≤ m) :
    projection I m ≫ sheafMap I h =
      projection I n := sorry

/-- The one-step sheaf transition `O / I ^ (n + 1) ⟶ O / I ^ n`. -/
@[stacks 0631 "ideal-power quotient transition"]
noncomputable abbrev sheafTransition
    (I : Subobject (unitModule J O)) (n : ℕ) :
    sheaf I (n + 1) ⟶
      sheaf I n :=
  sheafMap I n.le_succ

/-- The inverse system of sheaves `n ↦ O / I ^ n`. -/
noncomputable abbrev sheafSystem
    (I : Subobject (unitModule J O)) :
    ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w} :=
  Functor.ofOpSequence (sheafTransition I)

/-- The `n`th graded piece of the ideal-power filtration, represented intrinsically as the
kernel ideal sheaf of `O / I ^ (n + 1) ⟶ O / I ^ n`. -/
@[stacks 0631 "graded piece"]
noncomputable abbrev gradedPiece
    (I : Subobject (unitModule J O)) (n : ℕ) :
    SheafOfModules (SheafOfModules.RingedSite.ringSheaf J (sheaf I (n + 1))) :=
  KernelIdeal.sheaf (sheafTransition I n)

end Sheaf

end IdealSheaf.PowerQuotient

namespace IdealSheaf.TargetQuotient

/-- The image of `I(U)` in the target section ring under a map `O ⟶ O'`. -/
noncomputable def ideal
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) (U : Cᵒᵖ) :
    Ideal (O'.obj.obj U) :=
  Ideal.map (alpha.hom.app U).hom (IdealSheaf.sections I U)

/-- Target restrictions preserve the extended ideals of sections. -/
theorem ideal_le_comap
    (alpha : O ⟶ O') (I : Subobject (unitModule J O))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    ideal alpha I U ≤
      (ideal alpha I V).comap (O'.obj.map f).hom := sorry

/-- The section object of `O' / I O'`. -/
noncomputable abbrev sections
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) (U : Cᵒᵖ) :
    CommRingCat.{w} :=
  CommRingCat.of (O'.obj.obj U ⧸ ideal alpha I U)

/-- The restriction map on the sectionwise target quotient `O' / I O'`. -/
noncomputable def restriction
    (alpha : O ⟶ O') (I : Subobject (unitModule J O))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    sections alpha I U ⟶ sections alpha I V :=
  CommRingCat.ofHom <|
    Ideal.quotientMap (ideal alpha I V) (O'.obj.map f).hom
      (ideal_le_comap alpha I f)

/-- Identity restrictions act identically on target quotient sections. -/
theorem restriction_id
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) (U : Cᵒᵖ) :
    restriction alpha I (𝟙 U) =
      𝟙 (sections alpha I U) := sorry

/-- Composite restrictions act by the composite map on target quotient sections. -/
theorem restriction_comp
    (alpha : O ⟶ O') (I : Subobject (unitModule J O))
    {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    restriction alpha I (f ≫ g) =
      restriction alpha I f ≫
        restriction alpha I g := sorry

/-- The presheaf of sectionwise target quotients `O'(U) / I(U) O'(U)`. -/
noncomputable def presheaf
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) :
    Cᵒᵖ ⥤ CommRingCat.{w} where
  obj U := sections alpha I U
  map f := restriction alpha I f
  map_id U := restriction_id alpha I U
  map_comp f g := restriction_comp alpha I f g

/-- The quotient projection onto a target quotient section. -/
noncomputable def sectionProjection
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) (U : Cᵒᵖ) :
    O'.obj.obj U ⟶ sections alpha I U :=
  CommRingCat.ofHom (Ideal.Quotient.mk _)

/-- Target quotient projections commute with restrictions. -/
theorem sectionProjection_naturality
    (alpha : O ⟶ O') (I : Subobject (unitModule J O))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    O'.obj.map f ≫ sectionProjection alpha I V =
      sectionProjection alpha I U ≫
        restriction alpha I f := sorry

/-- The presheaf-level projection `O' ⟶ O' / I O'`. -/
noncomputable def presheafProjection
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) :
    O'.obj ⟶ presheaf alpha I where
  app U := sectionProjection alpha I U
  naturality {_ _} f :=
    sectionProjection_naturality alpha I f

section TargetQuotientSheaf

variable [HasWeakSheafify J CommRingCat.{w}]

/-- The target quotient sheaf `O' / I O'`. -/
noncomputable abbrev sheaf
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) :
    Sheaf J CommRingCat.{w} :=
  PresheafOfModules.commRingSheafification J
    (presheaf alpha I)

/-- The canonical target quotient projection `O' ⟶ O' / I O'`. -/
noncomputable def projection
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) :
    O' ⟶ sheaf alpha I :=
  { hom := presheafProjection alpha I ≫
      CategoryTheory.toSheafify J (presheaf alpha I) }

/-- The target quotient ring sheaf after forgetting commutativity. -/
noncomputable abbrev ringSheaf
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) :
    Sheaf J RingCat.{w} :=
  SheafOfModules.RingedSite.ringSheaf J (sheaf alpha I)

/-- The target quotient projection after forgetting commutativity. -/
noncomputable abbrev ringProjection
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) :
    SheafOfModules.RingedSite.ringSheaf J O' ⟶ ringSheaf alpha I :=
  SheafOfModules.RingedSite.ringSheafMap (projection alpha I)

end TargetQuotientSheaf

/-- The map from a source quotient section to the corresponding target quotient section. -/
noncomputable def sectionMap
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) (U : Cᵒᵖ) :
    IdealSheaf.Quotient.sections I U ⟶ sections alpha I U :=
  CommRingCat.ofHom <|
    Ideal.quotientMap (ideal alpha I U) (alpha.hom.app U).hom
      Ideal.le_comap_map

/-- The quotient maps induced by `alpha` commute with restrictions. -/
theorem sectionMap_naturality
    (alpha : O ⟶ O') (I : Subobject (unitModule J O))
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    IdealSheaf.Quotient.restriction I f ≫ sectionMap alpha I V =
      sectionMap alpha I U ≫
        restriction alpha I f := sorry

/-- The presheaf map `O / I ⟶ O' / I O'` induced by `alpha`. -/
noncomputable def presheafMap
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) :
    IdealSheaf.Quotient.presheaf I ⟶ presheaf alpha I where
  app U := sectionMap alpha I U
  naturality {_ _} f := sectionMap_naturality alpha I f

/-- The quotient projections and the induced presheaf map form the canonical square. -/
theorem presheafProjection_comp_map
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) :
    IdealSheaf.Quotient.presheafProjection I ≫ presheafMap alpha I =
      alpha.hom ≫ presheafProjection alpha I := sorry

section QuotientSheafMap

variable [HasWeakSheafify J CommRingCat.{w}]

/-- The quotient sheaf map `O / I ⟶ O' / I O'` induced by `alpha`. -/
noncomputable abbrev sheafMap
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) :
    IdealSheaf.Quotient.sheaf I ⟶ sheaf alpha I :=
  PresheafOfModules.commRingSheafificationMap J
    (presheafMap alpha I)

/-- The quotient sheaf map after forgetting commutativity. -/
@[stacks 0GLY "quotient map"]
noncomputable abbrev ringMap
    (alpha : O ⟶ O') (I : Subobject (unitModule J O)) :
    IdealSheaf.Quotient.ringSheaf I ⟶ ringSheaf alpha I :=
  SheafOfModules.RingedSite.ringSheafMap (sheafMap alpha I)

end QuotientSheafMap

end IdealSheaf.TargetQuotient

end SheafOfModules.RingedSite
