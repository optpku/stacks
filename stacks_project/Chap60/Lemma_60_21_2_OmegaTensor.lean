module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower.Pullback
public import stacks_project.Chap60.Lemma_60_18_2
public import stacks_project.Chap60.Definition_60_11_1_ModuleProperties
public import stacks_project.Chap60.Lemma_60_12_3_Differentials

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf
open PresheafOfModules

noncomputable section

universe u

/-- Tensor product of `𝒪_X`-modules, using the canonical sheafified tensor. -/
def schemeModulesTensor {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  SheafOfModules.RingedSite.moduleTensor (𝒪 := X.𝒪) M N

/-- Exterior power of an `𝒪_X`-module, sheafifying the sectionwise exterior power. -/
def schemeModulesExteriorPower {X : Scheme.{u}} (M : X.Modules) (i : ℕ) : X.Modules :=
  SheafOfModules.RingedSite.ExteriorPower.sheaf X.𝒪 M i

/-- Canonical pullback comparison isomorphism for tensor products of module sheaves. -/
def schemeModules_pullback_tensor {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules) :
    (pullback f).obj (schemeModulesTensor M N) ≅
      schemeModulesTensor ((pullback f).obj M) ((pullback f).obj N) :=
  RingedSpace.Hom.pullbackTensorIso f.toShHom M N

/-- Canonical pullback comparison for exterior powers of module sheaves. -/
def schemeModules_pullback_exteriorPower {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (i : ℕ) :
    (pullback f).obj (schemeModulesExteriorPower M i) ⟶
      schemeModulesExteriorPower ((pullback f).obj M) i :=
  RingedSpace.ExteriorPower.Pullback.comparison f.toShHom M i

/-- Pullback commutes with the sheafified exterior power. -/
instance schemeModules_pullback_exteriorPower_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (i : ℕ) : IsIso (schemeModules_pullback_exteriorPower f M i) := sorry

/-- Comparison morphism for a tensor of module morphisms along a scheme morphism. -/
def schemeModulesTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} {M' N' : X.Modules}
    (gM : (pullback f).obj M ⟶ M') (gN : (pullback f).obj N ⟶ N') :
    (pullback f).obj (schemeModulesTensor M N) ⟶ schemeModulesTensor M' N' :=
  (schemeModules_pullback_tensor f M N).hom ≫
    SheafOfModules.RingedSite.moduleTensorMap (𝒪 := X.𝒪) gM gN

/-- Comparison morphism for an exterior power of a module morphism along a scheme morphism. -/
def schemeModulesExteriorPowerComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} {M' : X.Modules} (g : (pullback f).obj M ⟶ M') (i : ℕ) :
    (pullback f).obj (schemeModulesExteriorPower M i) ⟶ schemeModulesExteriorPower M' i :=
  schemeModules_pullback_exteriorPower f M i ≫
    SheafOfModules.RingedSite.ExteriorPower.map X.𝒪 g i

/-- The scheme tensor uses the canonical tensor on module sheaves. -/
theorem schemeModulesTensor_eq {X : Scheme.{u}} (M N : X.Modules) :
    schemeModulesTensor M N = SheafOfModules.RingedSite.moduleTensor (𝒪 := X.𝒪) M N := sorry

/-- The scheme exterior power is the sheafification of its sectionwise construction. -/
theorem schemeModulesExteriorPower_eq {X : Scheme.{u}} (M : X.Modules) (i : ℕ) :
    schemeModulesExteriorPower M i =
      (RingedSpace.moduleSheafification X.toRingedSpace).obj
        (SheafOfModules.RingedSite.ExteriorPower.presheaf X.𝒪 M i) := sorry

/-- Exterior power `Ω^i_{X/S}` as a crystalline module sheaf on `Cris(X/S)`. -/
def crystallineOmegaPower
    {p : ℕ} [Fact (Nat.Prime p)]
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (i : ℕ) :
    CrisModuleSheaf S I γ h_compatible X x₀ where
  obj T := schemeModulesExteriorPower (Ω.module.obj T.obj.1) i
  comparison φ :=
    schemeModulesExteriorPowerComparison φ.hom.thickening (Ω.module.comparison φ.hom) i

/-- Evaluation of `Ω^i_{X/S}` on a small crystalline thickening. -/
theorem crystallineOmegaPower_obj
    {p : ℕ} [Fact (Nat.Prime p)]
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (i : ℕ) (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (crystallineOmegaPower Ω i).obj T =
      schemeModulesExteriorPower (Ω.module.obj T.obj.1) i :=
  sorry

/-- Tensor product of two crystalline module sheaves, formed objectwise over `𝒪_T`. -/
def crystallineTensor
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F G : CrisModuleSheaf S I γ h_compatible X x₀) :
    CrisModuleSheaf S I γ h_compatible X x₀ where
  obj T := schemeModulesTensor (F.obj T) (G.obj T)
  comparison φ :=
    schemeModulesTensorComparison φ.hom.thickening (F.comparison φ) (G.comparison φ)

/-- Evaluation of the objectwise tensor of crystalline module sheaves. -/
theorem crystallineTensor_obj
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (F G : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (crystallineTensor F G).obj T = schemeModulesTensor (F.obj T) (G.obj T) :=
  sorry

/-- The coefficient sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` on `Cris(X/S)`. -/
def crystallineTensorOmegaPower
    {p : ℕ} [Fact (Nat.Prime p)]
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))}
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (i : ℕ) :
    CrisModuleSheaf S I γ h_compatible X x₀ :=
  crystallineTensor F (crystallineOmegaPower Ω i)

/-- Evaluation of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` on a small crystalline thickening. -/
theorem crystallineTensorOmegaPower_obj
    {p : ℕ} [Fact (Nat.Prime p)]
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))}
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (i : ℕ) (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (crystallineTensorOmegaPower F Ω i).obj T =
      schemeModulesTensor (F.obj T) ((crystallineOmegaPower Ω i).obj T) :=
  sorry

namespace CrystallineModuleSheaf

variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- Restriction of a big crystalline module assignment to the small crystalline site. -/
def restrictCrystallineModule (F : CrystallineModuleSheaf S I γ h_compatible X x₀) :
    CrisModuleSheaf S I γ h_compatible X x₀ where
  obj T := F.obj T.obj.1
  comparison f := F.comparison f.hom

/-- Restriction retains the module sheaf on each thickening. -/
theorem restrictCrystallineModule_obj
    (F : CrystallineModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (restrictCrystallineModule F).obj T = F.obj T.obj.1 := sorry

/-- The intrinsic coherence and Zariski descent laws for a crystalline module assignment.
The open-immersion condition identifies its module sheaves with restrictions of one sheaf;
comparisons along general morphisms need not be isomorphisms. -/
structure IsCrisSheaf.{v}
    {S : Scheme.{v}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{v}} {x₀ : X ⟶ I.subscheme}
    (p : ℕ) [Fact (Nat.Prime p)]
    (s : S ⟶ Spec (.of (ULift.{v} (Int.LocalizationAtPrime p))))
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (F : CrisModuleSheaf S I γ h_compatible X x₀) : Prop where
  /-- Comparisons preserve identity morphisms, using canonical pullback identification. -/
  comparison_id (T : smallCrystallineSite S I γ h_compatible X x₀) :
    F.comparison (𝟙 T) = (pullbackId T.obj.1.thickening).hom.app (F.obj T)
  /-- Comparisons preserve composition, using the canonical pullback compositor. -/
  comparison_comp {T U V : smallCrystallineSite S I γ h_compatible X x₀}
      (f : T ⟶ U) (g : U ⟶ V) :
    F.comparison (f ≫ g) =
      (pullbackComp f.hom.thickening g.hom.thickening).inv.app (F.obj V) ≫
        (pullback f.hom.thickening).map (F.comparison g) ≫ F.comparison f
  /-- Restricting a thickening to an open restricts its assigned module sheaf. -/
  restriction {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U)
      (h_open : IsOpenImmersion f.hom.thickening) : IsIso (F.comparison f)
  /-- Global sections of the assignments satisfy descent on the crystalline site. -/
  descent : Presheaf.IsSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
    (toAbelianPresheaf S I γ h_compatible X x₀ F)

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- Recognize a genuine crystalline sheaf from its intrinsic comparison and descent laws. -/
def IsCrisSheaf.of (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (comparison_id : ∀ T : smallCrystallineSite S I γ h_compatible X x₀,
      F.comparison (𝟙 T) = (pullbackId T.obj.1.thickening).hom.app (F.obj T))
    (comparison_comp : ∀ {T U V : smallCrystallineSite S I γ h_compatible X x₀}
      (f : T ⟶ U) (g : U ⟶ V),
      F.comparison (f ≫ g) =
        (pullbackComp f.hom.thickening g.hom.thickening).inv.app (F.obj V) ≫
          (pullback f.hom.thickening).map (F.comparison g) ≫ F.comparison f)
    (restriction : ∀ {T U : smallCrystallineSite S I γ h_compatible X x₀}
      (f : T ⟶ U), IsOpenImmersion f.hom.thickening → IsIso (F.comparison f))
    (descent : Presheaf.IsSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (toAbelianPresheaf S I γ h_compatible X x₀ F)) : IsCrisSheaf p s h_p F :=
  { comparison_id, comparison_comp, restriction, descent }

/-- A genuine crystalline sheaf has both identity and composition compatibility. -/
theorem IsCrisSheaf.comparison_spec {F : CrisModuleSheaf S I γ h_compatible X x₀}
    (hF : IsCrisSheaf p s h_p F) :
    (∀ T : smallCrystallineSite S I γ h_compatible X x₀,
      F.comparison (𝟙 T) = (pullbackId T.obj.1.thickening).hom.app (F.obj T)) ∧
    (∀ {T U V : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U) (g : U ⟶ V),
      F.comparison (f ≫ g) =
        (pullbackComp f.hom.thickening g.hom.thickening).inv.app (F.obj V) ≫
          (pullback f.hom.thickening).map (F.comparison g) ≫ F.comparison f) := sorry

/-- A genuine crystalline sheaf restricts correctly to opens and satisfies descent. -/
theorem IsCrisSheaf.descent_spec {F : CrisModuleSheaf S I γ h_compatible X x₀}
    (hF : IsCrisSheaf p s h_p F) :
    (∀ {T U : smallCrystallineSite S I γ h_compatible X x₀} (f : T ⟶ U),
      IsOpenImmersion f.hom.thickening → IsIso (F.comparison f)) ∧
    Presheaf.IsSheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      (toAbelianPresheaf S I γ h_compatible X x₀ F) := sorry

/-- The underlying abelian sheaf of a coherent crystalline module assignment, with its
actual sections and comparison maps, rather than an unrelated sheafification. -/
def IsCrisSheaf.abelianSheaf {F : CrisModuleSheaf S I γ h_compatible X x₀}
    (hF : IsCrisSheaf p s h_p F) :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u} :=
  ⟨toAbelianPresheaf S I γ h_compatible X x₀ F, hF.descent⟩

/-- The abelian sheaf has exactly the sections and restriction maps induced by the assignment. -/
theorem IsCrisSheaf.abelianSheaf_obj {F : CrisModuleSheaf S I γ h_compatible X x₀}
    (hF : IsCrisSheaf p s h_p F) :
    (hF.abelianSheaf p s h_p).obj = toAbelianPresheaf S I γ h_compatible X x₀ F := sorry

/-- Sheafified tensor products preserve the intrinsic crystalline sheaf laws. -/
theorem crystallineTensor_isCrisSheaf (F G : CrisModuleSheaf S I γ h_compatible X x₀)
    (hF : IsCrisSheaf p s h_p F) (hG : IsCrisSheaf p s h_p G) :
    IsCrisSheaf p s h_p (crystallineTensor F G) := sorry

variable {h_I_quasiCoherent : I.toModule.IsQuasicoherent}

/-- Exterior powers of the genuine crystalline differential sheaf are genuine sheaves. -/
theorem crystallineOmegaPower_isCrisSheaf
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (hΩ : IsCrisSheaf p s h_p (restrictCrystallineModule Ω.module)) (i : ℕ) :
    IsCrisSheaf p s h_p (crystallineOmegaPower Ω i) := sorry

/-- The tensor coefficient is a genuine crystalline sheaf when its factors are genuine sheaves. -/
theorem crystallineTensorOmegaPower_isCrisSheaf
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (hF : IsCrisSheaf p s h_p F)
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (hΩ : IsCrisSheaf p s h_p (restrictCrystallineModule Ω.module)) (i : ℕ) :
    IsCrisSheaf p s h_p (crystallineTensorOmegaPower F Ω i) := sorry

/-- The actual abelian coefficient sheaf `F ⊗ Ω^i`, with sections computed by the
sheafified tensor and exterior-power constructions on each thickening. -/
def crystallineTensorOmegaPowerSheaf
    (F : CrisModuleSheaf S I γ h_compatible X x₀) (hF : IsCrisSheaf p s h_p F)
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (hΩ : IsCrisSheaf p s h_p (restrictCrystallineModule Ω.module)) (i : ℕ) :
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u} :=
  IsCrisSheaf.abelianSheaf p s h_p
    (crystallineTensorOmegaPower_isCrisSheaf p s h_p F hF Ω hΩ i)

/-- The coefficient sheaf retains the global-section presheaf of the tensor assignment,
including all of its comparison-induced restriction maps. -/
theorem crystallineTensorOmegaPowerSheaf_obj
    (F : CrisModuleSheaf S I γ h_compatible X x₀) (hF : IsCrisSheaf p s h_p F)
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (hΩ : IsCrisSheaf p s h_p (restrictCrystallineModule Ω.module)) (i : ℕ) :
    (crystallineTensorOmegaPowerSheaf p s h_p F hF Ω hΩ i).obj =
      toAbelianPresheaf S I γ h_compatible X x₀ (crystallineTensorOmegaPower F Ω i) := sorry

end CrystallineModuleSheaf

end
