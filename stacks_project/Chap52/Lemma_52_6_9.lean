module

public import stacks_project.Chap52.Lemma_52_6_8
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Koszul.Functoriality
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect
public import Mathlib.Algebra.Homology.Embedding.Restriction
public import ReasLib.CategoryTheory.Monoidal.Closed.Duality.HomotopyColimit

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.ExtendedCech
open scoped Pretriangulated.Opposite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.ExtendedCech

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/- The pointwise power is packaged as a compatible global section so that powered Koszul
   stages use actual section data rather than an existential representative. -/
/-- The value of a power of a global section is the corresponding pointwise power. -/
theorem sectionPow_naturality (s : (unitModule J O).sections) (n : ℕ)
    (U V : Cᵒᵖ) (g : U ⟶ V) :
    (unitModule J O).val.map g (sectionValue s U ^ n) = sectionValue s V ^ n := sorry

/-- The global section obtained by taking a pointwise power of a global section. -/
noncomputable def sectionPow
    (s : (unitModule J O).sections) (n : ℕ) : (unitModule J O).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ sectionValue s U ^ n)
    (fun {U V} g ↦ sectionPow_naturality s n U V g)

/-- Evaluation of a powered global section is pointwise exponentiation. -/
theorem sectionPow_apply (s : (unitModule J O).sections) (n : ℕ) (U : Cᵒᵖ) :
    (sectionPow s n).val U = sectionValue s U ^ n := sorry

/- The powered family map is the concrete map whose Koszul complex is used at stage `n`. -/
/-- The finite free family map for the `n`th powers of the chosen sections. -/
noncomputable def poweredFamilyMap
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    Arrow (ringedSiteModuleCategory J O) :=
  familyMap (fun i ↦ sectionPow (f i) n)

/-- The powered family map unfolds to the Čech family-map construction. -/
theorem poweredFamilyMap_def
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredFamilyMap f n = familyMap (fun i ↦ sectionPow (f i) n) := sorry

/-- Multiplication by a global section on a sheaf of modules. -/
noncomputable def globalSectionAction
    (s : (unitModule J O).sections) (M : ringedSiteModuleCategory J O) : M ⟶ M where
  val.app U := ModuleCat.ofHom
    (LinearMap.lsmul (O.obj.obj U) (M.val.obj U) (sectionValue s U))
  val.naturality _ := sorry

/-- The global-section action has the expected component on every object of the site. -/
theorem globalSectionAction_app
    (s : (unitModule J O).sections) (M : ringedSiteModuleCategory J O) (U : Cᵒᵖ) :
    (globalSectionAction s M).val.app U = ModuleCat.ofHom
      (LinearMap.lsmul (O.obj.obj U) (M.val.obj U) (sectionValue s U)) := sorry

/-- The diagonal endomorphism of the finite free module sheaf which multiplies generator `i`
by `f i`. -/
noncomputable def poweredFamilyStep
    {r : ℕ} (f : Fin r → (unitModule J O).sections) :
    (poweredFamilyMap f 1).left ⟶ (poweredFamilyMap f 1).left :=
  ((poweredFamilyMap f 1).left).freeHomEquiv.symm
    fun i ↦ SheafOfModules.sectionsMap
      (globalSectionAction (f i.down)
        (poweredFamilyMap f 1).left)
      (((poweredFamilyMap f 1).left).freeHomEquiv (𝟙 _) i)

/-- The powered family map, regarded as a linear form over the structure module. -/
noncomputable abbrev poweredLinearForm
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    Koszul.LinearForm O :=
  Over.mk ((unitModule J O).freeHomEquiv.symm
    (fun i : ULift.{u} (Fin r) ↦ sectionPow (f i.down) (n + 1)))

/-- The powered linear form uses exponent `n + 1` at zero-based stage `n`. -/
theorem poweredLinearForm_hom
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    (poweredLinearForm f n).hom = (poweredFamilyMap f (n + 1)).hom := sorry

/-- The diagonal free-module map intertwines the `(n + 2)`nd- and `(n + 1)`st-power
linear forms. -/
theorem poweredFamilyStep_comp
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredFamilyStep f ≫ (poweredLinearForm f n).hom =
      (poweredLinearForm f (n + 1)).hom := sorry

/-- The adjacent morphism from the `(n + 2)`nd-power linear form to the
`(n + 1)`st-power linear form. -/
noncomputable def poweredLinearFormStep
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredLinearForm f (n + 1) ⟶ poweredLinearForm f n :=
  Over.homMk (poweredFamilyStep f) (poweredFamilyStep_comp f n)

/-- The underlying map of an adjacent powered linear-form transition is the diagonal
free-module endomorphism. -/
theorem poweredLinearFormStep_left
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    (poweredLinearFormStep f n).left = poweredFamilyStep f := sorry

/-- The positive cochain model of the Koszul complex on the `(n + 1)`st powers of `f`;
degree `p` corresponds to exterior degree `r - p`. -/
noncomputable def poweredKoszulCochainStage
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    CochainComplex (ringedSiteModuleCategory J O) ℕ :=
  (((Koszul.complex O (poweredLinearForm f n).hom).extend
      (ComplexShape.embeddingUpIntLE (r : ℤ))).restriction
    ComplexShape.embeddingUpNat)

/-- The positive powered Koszul stage unfolds to the complementary cochain reindexing. -/
theorem poweredKoszulCochainStage_def
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulCochainStage f n =
      (((Koszul.complex O (poweredLinearForm f n).hom).extend
          (ComplexShape.embeddingUpIntLE (r : ℤ))).restriction
        ComplexShape.embeddingUpNat) := sorry

/-- The ordinary cochain model of the Koszul complex on the `(n + 1)`st powers, used before
passing to its positive dual orientation. -/
noncomputable def poweredKoszulChainStage
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    CochainComplex (ringedSiteModuleCategory J O) ℤ :=
  (Koszul.complex O (poweredLinearForm f n).hom).extend ComplexShape.embeddingDownNat

/-- The ordinary powered Koszul cochain model is the downward extension of its chain complex. -/
theorem poweredKoszulChainStage_def
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulChainStage f n =
      (Koszul.complex O (poweredLinearForm f n).hom).extend
        ComplexShape.embeddingDownNat := sorry

/-- The derived object represented by the ordinary Koszul complex on the `(n + 1)`st powers. -/
noncomputable def poweredKoszulChainDerived
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    RingedSiteDerived J O :=
  DerivedCategory.Q.obj (poweredKoszulChainStage f n)

/-- The ordinary powered Koszul derived stage is the localization of its explicit complex. -/
theorem poweredKoszulChainDerived_def
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulChainDerived f n =
      (DerivedCategory.Q :
        CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ RingedSiteDerived J O).obj
        (poweredKoszulChainStage f n) := sorry

/-- The adjacent transition in the ordinary powered Koszul cochain tower. -/
noncomputable def poweredKoszulChainStep
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulChainStage f (n + 1) ⟶ poweredKoszulChainStage f n :=
  (ComplexShape.embeddingDownNat.extendFunctor
    (ringedSiteModuleCategory J O)).map (Koszul.map O (poweredLinearFormStep f n))

/-- The ordinary successor transition is the extension of the Koszul map induced by the
diagonal powered-family morphism. -/
theorem poweredKoszulChainStep_def
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulChainStep f n =
      (ComplexShape.embeddingDownNat.extendFunctor
        (ringedSiteModuleCategory J O)).map (Koszul.map O (poweredLinearFormStep f n)) := sorry

/-- The adjacent derived transition is induced by the concrete diagonal powered-Koszul map. -/
noncomputable def poweredKoszulChainDerivedStep
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulChainDerived f (n + 1) ⟶ poweredKoszulChainDerived f n :=
  DerivedCategory.Q.map (poweredKoszulChainStep f n)

/-- The derived successor transition is the image of the explicit cochain transition. -/
theorem poweredKoszulChainDerivedStep_def
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulChainDerivedStep f n =
      DerivedCategory.Q.map (poweredKoszulChainStep f n) := sorry

/-- The derived powered-Koszul inverse system, including its canonical transition maps. -/
noncomputable def poweredKoszulChainSystem
    {r : ℕ} (f : Fin r → (unitModule J O).sections) :
    ℕᵒᵖ ⥤ RingedSiteDerived J O :=
  Functor.ofOpSequence (poweredKoszulChainDerivedStep f)

/-- Object `n` of the ordinary powered-Koszul inverse system is its `(n + 1)`st-power stage. -/
theorem poweredKoszulChainSystem_obj
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    (poweredKoszulChainSystem f).obj (Opposite.op n) =
      poweredKoszulChainDerived f n := sorry

/-- The successor map of the ordinary inverse system is its explicit derived Koszul map. -/
theorem poweredKoszulChainSystem_map_succ
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    (poweredKoszulChainSystem f).map (homOfLE (Nat.le_succ n)).op =
      poweredKoszulChainDerivedStep f n := sorry

end SheafOfModules.RingedSite.ExtendedCech

namespace RingedSite.Hom.ModuleDerived

open CategoryTheory.MonoidalCategory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}
variable [MonoidalCategory (RingedSiteDerived J O)]
variable [BraidedCategory (RingedSiteDerived J O)]

open SheafOfModules.RingedSite.ExtendedCech

/- The closed dual is made explicit here because the source's completion object also depends on a
   chosen closed structure; this avoids silently changing the dualized tower when that choice
   varies. -/
/-- The closed dual selected by an explicit monoidal-closed structure on the derived category. -/
noncomputable abbrev poweredKoszulDual
    (H : MonoidalClosed (RingedSiteDerived J O)) (X : RingedSiteDerived J O) :
    RingedSiteDerived J O :=
  @MonoidalClosed.dual (RingedSiteDerived J O) _ _ H X

/-- The explicit-owner dual bridge unfolds to the selected closed dual. -/
theorem poweredKoszulDual_def
    (H : MonoidalClosed (RingedSiteDerived J O)) (X : RingedSiteDerived J O) :
    poweredKoszulDual H X =
      @MonoidalClosed.dual (RingedSiteDerived J O) _ _ H X := sorry

/-- The positive powered-Koszul transition is the closed dual of the concrete adjacent map in
the ordinary powered-Koszul inverse system. -/
noncomputable def poweredKoszulStep
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulDual H (poweredKoszulChainDerived f n) ⟶
      poweredKoszulDual H (poweredKoszulChainDerived f (n + 1)) :=
  (MonoidalClosed.preOf H (poweredKoszulChainDerivedStep f n)).app
    (𝟙_ (RingedSiteDerived J O))

/-- The positive powered-Koszul stages and their actual dualized transition maps form a
sequential direct system. -/
noncomputable def poweredKoszulSystem
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections) :
    ℕ ⥤ RingedSiteDerived J O :=
  Functor.ofSequence (poweredKoszulStep H f)

/-- The `n`th object of the positive system is the dual of the ordinary Koszul complex on the
`(n + 1)`st powers. -/
theorem poweredKoszulSystem_obj
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    (poweredKoszulSystem H f).obj n =
      poweredKoszulDual H (poweredKoszulChainDerived f n) := sorry

/-- The successor map of the positive system is the dual of the concrete powered-Koszul
transition. -/
theorem poweredKoszulSystem_map_succ
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    (poweredKoszulSystem H f).map (homOfLE (Nat.le_succ n)) =
      poweredKoszulStep H f n := sorry

/-- The dual presentation of a positive stage agrees with the source-facing complementary
cochain grading whose degree `p` is exterior degree `r - p`. -/
theorem poweredKoszulSystem_obj_isPositiveStage
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    IsIsomorphic ((poweredKoszulSystem H f).obj n)
      ((CochainComplex.Nat.toDerived (ringedSiteModuleCategory J O)).obj
        (poweredKoszulCochainStage f n)) := sorry

/-- The canonical positive powered-Koszul system has the Čech complex as its homotopy colimit.
The stage index is zero-based, so stage `n` uses the `(n + 1)`st powers. -/
theorem poweredKoszulSystem_isHomotopyColimit
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections) :
    HomotopyColimit.IsOf (poweredKoszulSystem H f) (ExtendedCech.derived f) := sorry

/-- The source's `K_n`: the closed dual of the positive Koszul stage on the `(n + 1)`st powers. -/
noncomputable abbrev poweredKoszulDualStage
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    RingedSiteDerived J O :=
  poweredKoszulDual H ((poweredKoszulSystem H f).obj n)

/-- The Koszul object `K_n` is the dual of the `n`th positive powered stage. -/
theorem poweredKoszulDualStage_def
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    poweredKoszulDualStage H f n =
      poweredKoszulDual H ((poweredKoszulSystem H f).obj n) := sorry

/-- The inverse system whose `n`th stage is `K ⊗ᴸ K_n`. -/
noncomputable abbrev poweredKoszulTensorTower
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (K : RingedSiteDerived J O) : ℕᵒᵖ ⥤ RingedSiteDerived J O :=
  @MonoidalClosed.Dual.tensorTower (RingedSiteDerived J O) _ _ H
    (poweredKoszulSystem H f) K

/-- Stage `n` of the completion tower is exactly `K ⊗ᴸ K_n`. -/
theorem poweredKoszulTensorTower_obj
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (K : RingedSiteDerived J O) (n : ℕ) :
    (poweredKoszulTensorTower H f K).obj (Opposite.op n) =
      K ⊗ poweredKoszulDualStage H f n := sorry

/-- The source-facing inverse system whose stage `n` is `K ⊗ᴸ K_n`, with transition induced by
the concrete map between the `(n + 2)`nd- and `(n + 1)`st powered Koszul complexes. -/
noncomputable def poweredKoszulChainTensorStep
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (K : RingedSiteDerived J O) (n : ℕ) :
    K ⊗ poweredKoszulChainDerived f (n + 1) ⟶ K ⊗ poweredKoszulChainDerived f n :=
  K ◁ poweredKoszulChainDerivedStep f n

/-- The source-facing tensor transition is tensoring the powered Koszul transition with `K`. -/
theorem poweredKoszulChainTensorStep_def
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (K : RingedSiteDerived J O) (n : ℕ) :
    poweredKoszulChainTensorStep f K n = K ◁ poweredKoszulChainDerivedStep f n := sorry

/-- The canonical tensor tower on the ordinary powered Koszul derived stages. -/
noncomputable def poweredKoszulChainTensorTower
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (K : RingedSiteDerived J O) : ℕᵒᵖ ⥤ RingedSiteDerived J O :=
  @Functor.ofOpSequence (RingedSiteDerived J O) _
    (fun n ↦ K ⊗ poweredKoszulChainDerived f n)
    (poweredKoszulChainTensorStep f K)

/-- The object at `n` in the source-facing tensor tower is `K ⊗ᴸ K_n`. -/
theorem poweredKoszulChainTensorTower_obj
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (K : RingedSiteDerived J O) (n : ℕ) :
    (poweredKoszulChainTensorTower f K).obj (Opposite.op n) =
      K ⊗ poweredKoszulChainDerived f n := sorry

/-- The canonical bidual comparison gives a natural isomorphism of the ordinary and dualized
inverse systems. -/
theorem poweredKoszulTensorTowers_isomorphic
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (K : RingedSiteDerived J O) :
    IsIsomorphic (poweredKoszulChainTensorTower f K)
      (poweredKoszulTensorTower H f K) := sorry

/-- Every ordinary powered Koszul chain stage is strictly perfect, exhibiting the finite-free
Koszul data used by the closed-owner comparison. -/
theorem poweredKoszulChainStage_isStrictlyPerfect
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    SheafOfModules.CochainComplex.IsStrictlyPerfect (poweredKoszulChainStage f n) := sorry

/-- Strict perfectness of an ordinary powered Koszul stage gives its right-dualizability in the
selected closed monoidal structure. -/
theorem poweredKoszulChainDerived_isRightDualizable_of_isStrictlyPerfect
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ)
    (hK : SheafOfModules.CochainComplex.IsStrictlyPerfect (poweredKoszulChainStage f n)) :
    IsRightDualizable (poweredKoszulChainDerived f n) := sorry

/-- The canonical bidual map of every ordinary powered Koszul stage is invertible. -/
theorem poweredKoszulChainDerived_isIso_bidualComparison
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    IsIso (@MonoidalClosed.Dual.bidualComparison (RingedSiteDerived J O) _ _ _ H
      (poweredKoszulChainDerived f n)) := sorry

/-- Right-dualizability is the closed-owner criterion for invertibility of the Koszul bidual map. -/
theorem poweredKoszulChainDerived_isIso_bidualComparison_of_isRightDualizable
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ)
    (hK : IsRightDualizable (poweredKoszulChainDerived f n)) :
    IsIso (@MonoidalClosed.Dual.bidualComparison (RingedSiteDerived J O) _ _ _ H
      (poweredKoszulChainDerived f n)) := sorry

/-- The source's Koszul object `K_n`, defined as the dual of the positive stage, is isomorphic to
the ordinary powered Koszul derived stage via the canonical bidual comparison. -/
theorem poweredKoszulDualStage_isomorphic_chain
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    IsIsomorphic (poweredKoszulDualStage H f n) (poweredKoszulChainDerived f n) := sorry

/-- Every positive powered-Koszul stage is right-dualizable. -/
theorem poweredKoszulSystem_isRightDualizable
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (f : Fin r → (unitModule J O).sections) (n : ℕ) :
    IsRightDualizable ((poweredKoszulSystem H f).obj n) := sorry

/-- Lemma 52.6.9: if `I` is generated by the global sections `f`, the derived completion of
`K` is the homotopy limit of the canonical inverse system with stage `K ⊗ᴸ K_n`, where `K_n`
is the Koszul complex on `f₁^(n+1), …, fᵣ^(n+1)`. -/
@[stacks 0A0E]
theorem derivedCompletion_isHomotopyLimit
    (H : MonoidalClosed (RingedSiteDerived J O))
    {r : ℕ} (I : Subobject (unitModule J O))
    (f : Fin r → (unitModule J O).sections)
    (hgen : generatedIdeal f = I)
    (K : RingedSiteDerived J O) :
    HomotopyLimit.IsOf (poweredKoszulChainTensorTower f K)
      (CechCompletion.obj H f K) := sorry

end RingedSite.Hom.ModuleDerived
