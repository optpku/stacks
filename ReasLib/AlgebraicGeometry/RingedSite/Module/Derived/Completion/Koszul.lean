module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Koszul.Powers
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.Bifunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CompletionMap

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

set_option backward.privateInPublic true in
/-- Ordinary tensor totalization with a fixed left cochain complex of module sheaves. -/
private noncomputable def tensorComplexLeft
    (M : CochainComplex (ringedSiteModuleCategory J O) ℤ) :
    CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤
      CochainComplex (ringedSiteModuleCategory J O) ℤ :=
  (MonoidalCategory.curriedTensor (ringedSiteModuleCategory J O)).map₂CochainComplex.obj M

-- The exposed definitions unfold this private implementation helper without publishing its name.
set_option backward.privateInPublic true in
/-- The total tensor complex of a module-sheaf complex with the ordinary Koszul complex
on the `(n + 1)`st powers of a finite family of global sections. -/
noncomputable def poweredKoszulChainTensorComplex
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (M : CochainComplex (ringedSiteModuleCategory J O) ℤ) (n : ℕ) :
    CochainComplex (ringedSiteModuleCategory J O) ℤ :=
  (tensorComplexLeft M).obj (Koszul.poweredKoszulChainStage f n)

set_option backward.privateInPublic true in
/-- The tensor-complex transition induced by the diagonal powered-Koszul map from
exponent `n + 2` to exponent `n + 1`. -/
noncomputable def poweredKoszulChainTensorComplexStep
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (M : CochainComplex (ringedSiteModuleCategory J O) ℤ) (n : ℕ) :
    poweredKoszulChainTensorComplex f M (n + 1) ⟶
      poweredKoszulChainTensorComplex f M n :=
  (tensorComplexLeft M).map (Koszul.poweredKoszulChainStep f n)

/-- The derived tensor stage represented by tensoring a complex representative of `K`
with the ordinary Koszul complex on the `(n + 1)`st powers. -/
noncomputable def poweredKoszulChainTensorStage
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (K : RingedSiteDerived.{u, u, u, u} J O) (n : ℕ) :
    RingedSiteDerived.{u, u, u, u} J O :=
  (@DerivedCategory.Q (ringedSiteModuleCategory J O) _ _
    (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).obj
      (poweredKoszulChainTensorComplex f
        ((@DerivedCategory.Q (ringedSiteModuleCategory J O) _ _
          (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).objPreimage K) n)

/-- Any complex representative of a derived object computes its tensor stage with the
finite-free powered Koszul complex. -/
theorem poweredKoszulChainTensorStage_model
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (K : RingedSiteDerived.{u, u, u, u} J O)
    (M : CochainComplex (ringedSiteModuleCategory J O) ℤ)
    (e : (@DerivedCategory.Q (ringedSiteModuleCategory J O) _ _
      (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).obj M ≅ K) (n : ℕ) :
    IsIsomorphic (poweredKoszulChainTensorStage f K n)
      ((@DerivedCategory.Q (ringedSiteModuleCategory J O) _ _
        (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).obj
          (poweredKoszulChainTensorComplex f M n)) := sorry

/-- The adjacent powered Koszul transition after taking the derived tensor product with `K`.
The map goes from exponent `n + 2` to exponent `n + 1`. -/
noncomputable def poweredKoszulChainTensorStep
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (K : RingedSiteDerived.{u, u, u, u} J O) (n : ℕ) :
    poweredKoszulChainTensorStage f K (n + 1) ⟶
      poweredKoszulChainTensorStage f K n :=
  (@DerivedCategory.Q (ringedSiteModuleCategory J O) _ _
    (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).map
      (poweredKoszulChainTensorComplexStep f
        ((@DerivedCategory.Q (ringedSiteModuleCategory J O) _ _
          (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).objPreimage K) n)

/-- The derived tensor transition is the localization of the concrete tensor-complex
transition. -/
theorem poweredKoszulChainTensorStep_def
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (K : RingedSiteDerived.{u, u, u, u} J O) (n : ℕ) :
    poweredKoszulChainTensorStep f K n =
      (@DerivedCategory.Q (ringedSiteModuleCategory J O) _ _
        (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).map
          (poweredKoszulChainTensorComplexStep f
            ((@DerivedCategory.Q (ringedSiteModuleCategory J O) _ _
              (moduleCategoryHasDerivedCategory (J := J) (𝒪 := O))).objPreimage K) n) := sorry

/-- The inverse system of derived tensor products of `K` with the ordinary Koszul complexes
on successive positive powers of a finite family of global sections. -/
noncomputable def poweredKoszulChainTensorTower
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (K : RingedSiteDerived.{u, u, u, u} J O) : ℕᵒᵖ ⥤ RingedSiteDerived.{u, u, u, u} J O :=
  Functor.ofOpSequence (poweredKoszulChainTensorStep f K)

/-- Stage `n` of the tensor tower is the derived tensor product with the Koszul complex on
the `(n + 1)`st powers. -/
theorem poweredKoszulChainTensorTower_obj
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (K : RingedSiteDerived.{u, u, u, u} J O) (n : ℕ) :
    (poweredKoszulChainTensorTower f K).obj (Opposite.op n) =
      poweredKoszulChainTensorStage f K n := sorry

/-- The successor map of the tensor tower is the derived tensor image of the diagonal
powered Koszul transition. -/
theorem poweredKoszulChainTensorTower_map_succ
    {r : ℕ} (f : Fin r → (unitModule J O).sections)
    (K : RingedSiteDerived.{u, u, u, u} J O) (n : ℕ) :
    (poweredKoszulChainTensorTower f K).map (homOfLE (Nat.le_succ n)).op =
      poweredKoszulChainTensorStep f K n := sorry

/-- Derived completion along an ideal generated by finitely many global sections is the
homotopy limit of derived tensor products with the ordinary powered Koszul complexes. -/
theorem derivedCompletion_isHomotopyLimit
    {r : ℕ} (I : Subobject (unitModule J O))
    (f : Fin r → (unitModule J O).sections)
    (hgen : ExtendedCech.generatedIdeal f = I)
    (K Khat : RingedSiteDerived.{u, u, u, u} J O) (η : K ⟶ Khat)
    (hη : IsDerivedCompletion.{u, u, u, u} I η) :
    HomotopyLimit.IsOf (poweredKoszulChainTensorTower f K) Khat := sorry

end RingedSite.Hom.ModuleDerived
