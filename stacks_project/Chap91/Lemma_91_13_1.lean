module

public import stacks_project.Chap91.Lemma_91_13_1_Diagram
public import stacks_project.Chap91.Lemma_91_13_1_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Obstruction and torsor of fillers of a relative first-order thickening diagram

Given the commutative first-order cube 91.13.1.1 of ringed topoi and a `g⁻¹𝒪₁`-module
map `ν` making 91.13.1.2, with front and back solutions of 91.13.0.1, there is a canonical
class in `Ext⁽1⁾(Lg^* NL(f₁), 𝒢₂)` that vanishes iff a morphism of ringed topoi
`(Sh(C'₂), 𝒪'₂) ⟶ (Sh(C'₁), 𝒪'₁)` fits the cube compatibly with `ν`. When nonempty,
those morphisms form a principal homogeneous space under `Hom(Ω(f₁), g_* 𝒢₂)`.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open scoped DerivedExt SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O1 O1' OB1 OB1' O2 O2' OB2 OB2' : Sheaf J CommRingCat.{u}}
variable {πO1 : O1' ⟶ O1} {πB1 : OB1' ⟶ OB1}
variable {πO2 : O2' ⟶ O2} {πB2 : OB2' ⟶ OB2}
variable [IsFirstOrderThickening πO1] [IsFirstOrderThickening πB1]
variable [IsFirstOrderThickening πO2] [IsFirstOrderThickening πB2]

/-- Lemma 91.13.1 (1) Given a commutative diagram of morphisms of ringed topoi 91.13.1.1
whose horizontal arrows are first-order thickenings, and a map of `g⁻¹𝒪₁`-modules
`ν : g⁻¹𝒢₁ ⟶ 𝒢₂` making 91.13.1.2, with front and back solutions of 91.13.0.1, after
identifying underlying topoi the canonical class `mapObstruction D` in
`Ext⁽1⁾(Lg^* NL(f₁), 𝒢₂)` vanishes if and only if there exists a morphism of ringed
topoi `(Sh(C'₂), 𝒪'₂) ⟶ (Sh(C'₁), 𝒪'₁)` fitting into 91.13.1.1 compatibly with `ν`. -/
@[stacks 08UG]
theorem mapObstruction_eq_zero_iff (D : RelativeDiagram πO1 πB1 πO2 πB2) :
    mapObstruction D = 0 ↔ Nonempty (FittingMap D) := sorry

/-- Lemma 91.13.1 (2) If there exists a morphism `(Sh(C'₂), 𝒪'₂) ⟶ (Sh(C'₁), 𝒪'₁)`
fitting into 91.13.1.1 compatibly with `ν`, the set of all such morphisms is a principal
homogeneous space under `Hom_{𝒪₁}(Ω(f₁), g_* 𝒢₂)`, equivalently
`Hom_{𝒪₂}(g^* Ω(f₁), 𝒢₂)` via `homOmegaPushforwardEquiv` and
`Ext⁽0⁾(Lg^* NL(f₁), 𝒢₂)` via bijective `homOmegaExtZero`. -/
@[stacks 08UG]
theorem fittingMap_principalHomogeneous (D : RelativeDiagram πO1 πB1 πO2 πB2)
    (φ φ' : FittingMap D) :
    ∃! α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2),
      perturb α φ = φ' := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
