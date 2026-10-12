/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor powers of module sheaves on a ringed site

The tensor power is defined as a functor on the module-sheaf category.  This makes its action on
morphisms available without rebuilding a recursive map, and leaves ringed spaces and schemes as
thin specializations of the topology-independent owner.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (𝒪 : Sheaf J CommRingCat.{w})

/-- The degree-`n` tensor-power endofunctor on module sheaves over a commutative ringed site. -/
@[stacks 01CK "tensor-power functor on a ringed site"]
noncomputable abbrev functor : ℕ →
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 ⥤
      ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  tensorPowerWithDegreeZeroFunctor (unitModule J 𝒪)

/-- The degree-`n` tensor power of a module sheaf on a commutative ringed site. -/
@[stacks 01CK "tensor power of a module sheaf on a ringed site"]
noncomputable abbrev sheaf
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n : ℕ) :
    ringedSiteModuleCategory.{u, v, w, w} J 𝒪 :=
  (functor 𝒪 n).obj F

/-- The morphism on degree-`n` tensor powers induced by a module-sheaf morphism. -/
@[stacks 01CK "morphism on tensor powers on a ringed site"]
noncomputable abbrev map
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (f : F ⟶ G) (n : ℕ) :
    sheaf 𝒪 F n ⟶ sheaf 𝒪 G n :=
  (functor 𝒪 n).map f

/-- The zeroth tensor power is the structure module. -/
@[simp, stacks 01CK "zeroth tensor power on a ringed site"]
theorem sheaf_zero
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    sheaf 𝒪 F 0 = unitModule J 𝒪 := sorry

/-- Tensor powers satisfy the left-recursive successor formula. -/
@[simp, stacks 01CK "successor tensor power on a ringed site"]
theorem sheaf_succ
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n : ℕ) :
    sheaf 𝒪 F (n + 1) = tensorObj F (sheaf 𝒪 F n) := sorry

/-- The zeroth tensor-power map is the identity of the structure module. -/
@[simp, stacks 01CK "zeroth tensor-power map on a ringed site"]
theorem map_zero
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (f : F ⟶ G) :
    map 𝒪 f 0 = 𝟙 _ := sorry

/-- Tensor-power maps satisfy the left-recursive successor formula. -/
@[simp, stacks 01CK "successor tensor-power map on a ringed site"]
theorem map_succ
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (f : F ⟶ G) (n : ℕ) :
    map 𝒪 f (n + 1) = f ⊗ₘ map 𝒪 f n := sorry

/-- The first tensor power is canonically isomorphic to the original module sheaf. -/
@[stacks 01CK "first tensor power on a ringed site"]
noncomputable def oneIso
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    sheaf 𝒪 F 1 ≅ F :=
  (Iso.refl F ⊗ᵢ unitIsoTensorUnit (J := J) (𝒪 := 𝒪)) ≪≫ ρ_ F

/-- The canonical comparison from the ambient monoidal tensor power to the tensor power whose
zeroth term is the structure module. -/
@[stacks 01CK "monoidal comparison for tensor powers"]
noncomputable abbrev monoidalComparison
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    (n : ℕ) → tensorPower F n ⟶ sheaf 𝒪 F n
  := fun n ↦
    (tensorPowerWithDegreeZeroMapIso
      (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)) (Iso.refl F) n).inv

namespace monoidalComparison

/-- The structural inverse of the tensor-power comparison, recursively built from the explicit
inverse tensor-unit comparison. -/
@[stacks 01CK "inverse monoidal comparison for tensor powers"]
noncomputable abbrev inv
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    (n : ℕ) → sheaf 𝒪 F n ⟶ tensorPower F n
  := fun n ↦
    (tensorPowerWithDegreeZeroMapIso
      (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)) (Iso.refl F) n).hom

/-- In degree zero, the structural inverse is the named inverse tensor-unit comparison. -/
@[simp, stacks 01CK "inverse monoidal comparison in degree zero"]
theorem inv_zero
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    inv 𝒪 F 0 = unitModuleToTensorUnit (J := J) (𝒪 := 𝒪) := sorry

/-- The structural inverse is recursive in successor degree. -/
@[simp, stacks 01CK "inverse monoidal comparison in successor degree"]
theorem inv_succ
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n : ℕ) :
    inv 𝒪 F (n + 1) = 𝟙 F ⊗ₘ inv 𝒪 F n := sorry

/-- The tensor-power comparison followed by its structural inverse is the identity. -/
@[simp, stacks 01CK "monoidal tensor-power comparison forward-inverse law"]
theorem hom_inv_id
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n : ℕ) :
    monoidalComparison 𝒪 F n ≫ inv 𝒪 F n = 𝟙 _ := sorry

/-- The structural inverse followed by the tensor-power comparison is the identity. -/
@[simp, stacks 01CK "monoidal tensor-power comparison inverse-forward law"]
theorem inv_hom_id
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n : ℕ) :
    inv 𝒪 F n ≫ monoidalComparison 𝒪 F n = 𝟙 _ := sorry

/-- The comparison between ambient and structure-module tensor powers as explicit isomorphism
data. -/
@[stacks 01CK "monoidal tensor-power comparison isomorphism"]
noncomputable abbrev iso
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n : ℕ) :
    tensorPower F n ≅ sheaf 𝒪 F n :=
  (tensorPowerWithDegreeZeroMapIso
    (unitIsoTensorUnit (J := J) (𝒪 := 𝒪)) (Iso.refl F) n).symm

/-- The forward map of the tensor-power comparison isomorphism is the canonical comparison. -/
@[simp, stacks 01CK "monoidal tensor-power comparison isomorphism hom"]
theorem iso_hom
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n : ℕ) :
    (iso 𝒪 F n).hom = monoidalComparison 𝒪 F n := sorry

/-- The inverse map of the tensor-power comparison isomorphism is the structural inverse. -/
@[simp, stacks 01CK "monoidal tensor-power comparison isomorphism inverse"]
theorem iso_inv
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n : ℕ) :
    (iso 𝒪 F n).inv = inv 𝒪 F n := sorry

/-- The forward maps of the tensor-power comparison isomorphisms are natural in the module
sheaf. -/
@[stacks 01CK "naturality of monoidal tensor-power comparison isomorphisms"]
theorem iso_naturality
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (f : F ⟶ G) (n : ℕ) :
    tensorPowerMap f n ≫ (iso 𝒪 G n).hom =
      (iso 𝒪 F n).hom ≫ map 𝒪 f n := sorry

end monoidalComparison

/-- In degree zero, the monoidal tensor-power comparison is the tensor-unit comparison. -/
@[simp, stacks 01CK "monoidal tensor-power comparison in degree zero"]
theorem monoidalComparison_zero
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :
    monoidalComparison 𝒪 F 0 =
      tensorUnitToUnitModule (J := J) (𝒪 := 𝒪) := sorry

/-- The monoidal tensor-power comparison is recursive in successor degree. -/
@[simp, stacks 01CK "monoidal tensor-power comparison in successor degree"]
theorem monoidalComparison_succ
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n : ℕ) :
    monoidalComparison 𝒪 F (n + 1) =
      𝟙 F ⊗ₘ monoidalComparison 𝒪 F n := sorry

/-- The monoidal tensor-power comparison is natural in the module sheaf. -/
@[stacks 01CK "naturality of the monoidal tensor-power comparison"]
theorem monoidalComparison_naturality
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (f : F ⟶ G) (n : ℕ) :
    tensorPowerMap f n ≫ monoidalComparison 𝒪 G n =
      monoidalComparison 𝒪 F n ≫ map 𝒪 f n := sorry

/-- The degree-`n` comparisons assemble into a natural isomorphism of module-sheaf functors. -/
@[stacks 01CK "natural isomorphism of ringed-site tensor-power comparisons"]
noncomputable def monoidalComparisonNatIso (n : ℕ) :
    tensorPowerFunctor
        (ringedSiteModuleCategory.{u, v, w, w} J 𝒪) n ≅
      functor 𝒪 n :=
  NatIso.ofComponents
    (fun F ↦ monoidalComparison.iso 𝒪 F n)
    (fun f ↦ monoidalComparison.iso_naturality 𝒪 f n)

/-- The structural inverse comparison is natural in the module sheaf. -/
@[stacks 01CK "naturality of the inverse monoidal tensor-power comparison"]
theorem monoidalComparison_inv_naturality
    {F G : ringedSiteModuleCategory.{u, v, w, w} J 𝒪} (f : F ⟶ G) (n : ℕ) :
    map 𝒪 f n ≫ monoidalComparison.inv 𝒪 G n =
      monoidalComparison.inv 𝒪 F n ≫ tensorPowerMap f n := sorry

/-- The monoidal tensor-power comparison is invertible in every degree. -/
@[stacks 01CK "invertibility of the monoidal tensor-power comparison"]
noncomputable instance monoidalComparison_isIso
    (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n : ℕ) :
    IsIso (monoidalComparison 𝒪 F n) :=
  (monoidalComparison.iso 𝒪 F n).isIso_hom

end SheafOfModules.RingedSite.TensorPower


