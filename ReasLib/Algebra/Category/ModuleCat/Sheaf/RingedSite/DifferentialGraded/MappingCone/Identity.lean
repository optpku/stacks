/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.MappingCone
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Regular
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.UnitSection

/-!
# The identity mapping-cone representative

This leaf describes morphisms out of the mapping cone of the identity of the regular DG module by
compatible unit-section pairs in degrees `0` and `-1`.  It exposes both directions as concrete data,
together with computation and postcomposition APIs.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.MappingCone.Identity

section Pair

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {𝒜 : DGA(𝒪)} {ℳ N P : Mod(𝒜, d)}

/-- A degree-`0`/degree-`-1` pair of unit sections of a DG module. -/
def Pair (ℳ : Mod(𝒜, d)) :=
  (unitModule J 𝒪 ⟶ ℳ 0) ×
    (unitModule J 𝒪 ⟶ ℳ (-1))

namespace Pair

/-- The differential compatibility condition on an identity-cone pair. -/
def Compatible (p : Pair ℳ) : Prop :=
  p.1 = p.2 ≫ ℳ.toComplex.d (-1) 0

/-- Compatibility for an explicitly presented pair. -/
@[simp] theorem compatible_mk
    (x : unitModule J 𝒪 ⟶ ℳ 0)
    (y : unitModule J 𝒪 ⟶ ℳ (-1)) :
    Compatible (x, y) ↔ x = y ≫ ℳ.toComplex.d (-1) 0 := sorry

/-- Postcomposition transports an identity-cone pair along a DG-module morphism. -/
def map (p : Pair ℳ) (f : ℳ ⟶ N) : Pair N :=
  (p.1 ≫ f.toCochainMap.f 0,
    p.2 ≫ f.toCochainMap.f (-1))

/-- Postcomposition preserves the compatibility relation. -/
theorem map_compatible (p : Pair ℳ) (hp : p.Compatible) (f : ℳ ⟶ N) :
    (p.map f).Compatible := sorry

/-- Mapping a pair by the identity morphism leaves it unchanged. -/
@[simp] theorem map_id (p : Pair ℳ) :
    p.map (𝟙 ℳ) = p := sorry

/-- Mapping a pair respects composition of DG-module morphisms. -/
@[simp] theorem map_comp (p : Pair ℳ) (f : ℳ ⟶ N) (g : N ⟶ P) :
    (p.map f).map g = p.map (f ≫ g) := sorry

end Pair

/-- The subtype of identity-cone pairs satisfying differential compatibility. -/
def CompatiblePair (ℳ : Mod(𝒜, d)) :=
  {p : Pair ℳ // p.Compatible}

namespace CompatiblePair

/-- Postcomposition transports a compatible pair along a DG-module morphism. -/
noncomputable def map (p : CompatiblePair ℳ) (f : ℳ ⟶ N) : CompatiblePair N :=
  ⟨p.val.map f, p.val.map_compatible p.property f⟩

/-- The value of a mapped compatible pair is the mapped underlying pair. -/
@[simp] theorem map_val (p : CompatiblePair ℳ) (f : ℳ ⟶ N) :
    (p.map f).val = p.val.map f := sorry

/-- Mapping a compatible pair by the identity morphism leaves it unchanged. -/
@[simp] theorem map_id (p : CompatiblePair ℳ) :
    p.map (𝟙 ℳ) = p := sorry

/-- Mapping compatible pairs respects composition. -/
@[simp] theorem map_comp (p : CompatiblePair ℳ) (f : ℳ ⟶ N) (g : N ⟶ P) :
    (p.map f).map g = p.map (f ≫ g) := sorry

end CompatiblePair

end Pair

section Cone

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable {𝒜 : DGA(𝒪)} {ℳ N : Mod(𝒜, d)}

/-- The mapping cone of the identity of the regular right DG module. -/
noncomputable def cone (𝒜 : DGA(𝒪)) : Mod(𝒜, d) :=
  mappingCone (𝟙 𝒜.regularModule)

/-- The degree-`n` term of the identity cone. -/
@[simp] theorem cone_X (𝒜 : DGA(𝒪)) (n : ℤ) :
    (cone 𝒜).toComplex.X n =
      (𝒜.toComplex.X n ⊞ 𝒜.toComplex.X (n + 1)) := sorry

/-- The differential of the identity cone in the canonical biproduct coordinates. -/
theorem cone_d (𝒜 : DGA(𝒪)) (n : ℤ) :
    (cone 𝒜).toComplex.d n (n + 1) =
      Biprod.ofComponents
        (𝒜.toComplex.d n (n + 1))
        0
        (𝟙 (𝒜.toComplex.X (n + 1)))
        (-𝒜.toComplex.d (n + 1) ((n + 1) + 1)) := sorry

/-- The degree-`0` canonical unit section of the identity cone. -/
noncomputable def zeroUnit (𝒜 : DGA(𝒪)) :
    unitModule J 𝒪 ⟶ cone 𝒜 0 :=
  𝒜.oneFromUnitModule ≫ biprod.inl ≫
    eqToHom (mappingCone_X (𝟙 𝒜.regularModule) 0).symm

/-- The degree-`-1` canonical unit section of the identity cone. -/
noncomputable def negOneUnit (𝒜 : DGA(𝒪)) :
    unitModule J 𝒪 ⟶ cone 𝒜 (-1) :=
  𝒜.oneFromUnitModule ≫ biprod.inr ≫
    eqToHom (mappingCone_X (𝟙 𝒜.regularModule) (-1)).symm

/-- The pair obtained by evaluating a morphism on the two canonical unit sections. -/
noncomputable def pair (f : cone 𝒜 ⟶ ℳ) : Pair ℳ :=
  (zeroUnit 𝒜 ≫ f.toCochainMap.f 0,
    negOneUnit 𝒜 ≫ f.toCochainMap.f (-1))

/-- Degree-`0` evaluation formula for the pair attached to a cone morphism. -/
@[simp] theorem pair_zero (f : cone 𝒜 ⟶ ℳ) :
    (pair f).1 = zeroUnit 𝒜 ≫ f.toCochainMap.f 0 := sorry

/-- Degree-`-1` evaluation formula for the pair attached to a cone morphism. -/
@[simp] theorem pair_negOne (f : cone 𝒜 ⟶ ℳ) :
    (pair f).2 = negOneUnit 𝒜 ≫ f.toCochainMap.f (-1) := sorry

/-- Every morphism out of the identity cone gives a compatible pair. -/
theorem pair_compatible (f : cone 𝒜 ⟶ ℳ) :
    (pair f).Compatible := sorry

/-- The compatible pair attached to a morphism out of the identity cone. -/
noncomputable def compatiblePair (f : cone 𝒜 ⟶ ℳ) : CompatiblePair ℳ :=
  ⟨pair f, pair_compatible f⟩

/-- Forgetting compatibility recovers the explicit pair. -/
@[simp] theorem compatiblePair_val (f : cone 𝒜 ⟶ ℳ) :
    (compatiblePair f).val = pair f := sorry

/-- Evaluation on the canonical pair is natural under postcomposition. -/
@[simp] theorem pair_comp (f : cone 𝒜 ⟶ ℳ) (g : ℳ ⟶ N) :
    pair (f ≫ g) = (pair f).map g := sorry

/-- Compatible-pair evaluation is natural under postcomposition. -/
@[simp] theorem compatiblePair_comp (f : cone 𝒜 ⟶ ℳ) (g : ℳ ⟶ N) :
    compatiblePair (f ≫ g) = (compatiblePair f).map g := sorry

namespace CompatiblePair

/-- The degree-`n` component of the morphism represented by a compatible pair. -/
noncomputable def homComponent (p : CompatiblePair ℳ) (n : ℤ) :
    (cone 𝒜).toComplex.X n ⟶ ℳ.toComplex.X n :=
  eqToHom (mappingCone_X (𝟙 𝒜.regularModule) n) ≫
    biprod.desc
      (UnitSection.action p.val.1 n ≫
        eqToHom (congrArg ℳ.toComplex.X (zero_add n)))
      (eqToHom (congrArg 𝒜.toComplex.X (add_comm n 1)) ≫
        UnitSection.action p.val.2 (1 + n) ≫
        eqToHom (congrArg ℳ.toComplex.X (neg_add_cancel_left 1 n)))

/-- The represented degreewise maps commute with the differentials. -/
theorem homComponent_comm (p : CompatiblePair ℳ) :
    ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      homComponent p i ≫ ℳ.toComplex.d i j =
        (cone 𝒜).toComplex.d i j ≫ homComponent p j := sorry

/-- The represented degreewise maps commute with the right DG-algebra action. -/
theorem homComponent_smul (p : CompatiblePair ℳ) (n m : ℤ) :
    (cone 𝒜).smul n m ≫ homComponent p (n + m) =
      (homComponent p n ▷ 𝒜.toComplex.X m) ≫ ℳ.smul n m := sorry

/-- The concrete DG-module morphism represented by a compatible pair. -/
noncomputable def hom (p : CompatiblePair ℳ) : cone 𝒜 ⟶ ℳ where
  toCochainMap :=
    { f := homComponent p
      comm' := homComponent_comm p }
  comm := homComponent_smul p

/-- The degreewise component of the morphism represented by a compatible pair. -/
@[simp] theorem hom_f (p : CompatiblePair ℳ) (n : ℤ) :
    p.hom.toCochainMap.f n = p.homComponent n := sorry

/-- Evaluating the represented morphism recovers the compatible pair. -/
@[simp] theorem hom_spec (p : CompatiblePair ℳ) :
    compatiblePair p.hom = p := sorry

/-- Reconstructing a morphism from its compatible pair recovers the morphism. -/
@[simp] theorem hom_compatiblePair (f : cone 𝒜 ⟶ ℳ) :
    (compatiblePair f).hom = f := sorry

/-- The represented morphism is unique with its compatible pair. -/
theorem hom_unique (p : CompatiblePair ℳ) (f : cone 𝒜 ⟶ ℳ)
    (hf : compatiblePair f = p) :
    f = p.hom := sorry

/-- Representation by compatible pairs is natural under postcomposition. -/
@[simp] theorem hom_map (p : CompatiblePair ℳ) (f : ℳ ⟶ N) :
    (p.map f).hom = p.hom ≫ f := sorry

/-- Every compatible pair is represented by a unique morphism out of the identity cone. -/
theorem existsUnique_hom (p : CompatiblePair ℳ) :
    ∃! f : cone 𝒜 ⟶ ℳ, compatiblePair f = p := sorry

end CompatiblePair

/-- Morphisms out of the identity cone are equivalent to compatible pairs. -/
noncomputable def homEquiv (𝒜 : DGA(𝒪)) (ℳ : Mod(𝒜, d)) :
    (cone 𝒜 ⟶ ℳ) ≃ CompatiblePair ℳ where
  toFun := compatiblePair
  invFun := CompatiblePair.hom
  left_inv := CompatiblePair.hom_compatiblePair
  right_inv := CompatiblePair.hom_spec

/-- The forward map of the representation equivalence is compatible-pair evaluation. -/
@[simp] theorem homEquiv_apply (f : cone 𝒜 ⟶ ℳ) :
    homEquiv 𝒜 ℳ f = compatiblePair f := sorry

/-- The inverse map of the representation equivalence is the explicit represented morphism. -/
@[simp] theorem homEquiv_symm_apply (p : CompatiblePair ℳ) :
    (homEquiv 𝒜 ℳ).symm p = p.hom := sorry

namespace Pair

/-- A compatible explicit pair comes from a unique morphism out of the identity cone. -/
theorem existsUnique_hom (p : Pair ℳ) (hp : p.Compatible) :
    ∃! f : cone 𝒜 ⟶ ℳ, pair f = p := sorry

/-- An explicit pair is uniquely represented exactly when it is compatible. -/
theorem existsUnique_hom_iff_compatible (p : Pair ℳ) :
    (∃! f : cone 𝒜 ⟶ ℳ, pair f = p) ↔ p.Compatible := sorry

end Pair

/-- Compatible-pair evaluation is bijective. -/
theorem compatiblePair_bijective :
    Function.Bijective (compatiblePair : (cone 𝒜 ⟶ ℳ) → CompatiblePair ℳ) := sorry

end Cone

end SheafOfModules.RingedSite.DifferentialGradedModule.MappingCone.Identity
