/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Derivation
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative differentials on a ringed site

This file owns the sheafification of the canonical presheaf of relative differentials.  The
construction is site-generic; topological-space and ringed-space APIs should be specializations
of this owner.
-/

@[expose] public section

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction
open scoped RelativeDerivation

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O₁ O₂ : Sheaf J CommRingCat.{w}}

/-- The sheaf of relative differentials of `O₂` over `O₁`, obtained by sheafifying the
canonical presheaf of Kähler differentials. -/
@[stacks 04BN, stacks 08RP "topological-space specialization"]
abbrev relativeDifferentials (φ : O₁ ⟶ O₂) :
    SheafOfModules (ringSheaf J O₂) :=
  (PresheafOfModules.sheafification
    (𝟙 (ringSheaf J O₂).obj)).obj (relativeDifferentials' φ.hom)

@[inherit_doc relativeDifferentials]
scoped[SheafOfModules.RingedSite] notation:max "Ω(" φ ")" =>
  SheafOfModules.RingedSite.relativeDifferentials φ

open scoped SheafOfModules.RingedSite

/-- The relative-differentials sheaf is the sheafification of the canonical presheaf owner. -/
@[stacks 08TD]
theorem relativeDifferentials_def (φ : O₁ ⟶ O₂) :
    Ω(φ) =
      (PresheafOfModules.sheafification
        (𝟙 (ringSheaf J O₂).obj)).obj (relativeDifferentials' φ.hom) := sorry

/-- The universal derivation `O₂ ⟶ Ω(φ)`. -/
@[stacks 08RP "universal derivation"]
def relativeDifferential (φ : O₁ ⟶ O₂) :
    Der[φ ; Ω(φ)] :=
  (derivation' φ.hom).postcomp
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J O₂).obj)).unit.app
      (relativeDifferentials' φ.hom))

/-- The morphism from `Ω(φ)` induced by a target `φ`-derivation. -/
def relativeDifferentialDesc (φ : O₁ ⟶ O₂)
    {F : SheafOfModules (ringSheaf J O₂)} (D : Der[φ ; F]) :
    Ω(φ) ⟶ F :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (ringSheaf J O₂).obj)).symm ((isUniversal' φ.hom).desc D)

/-- The descended morphism factors the target derivation through the universal derivation. -/
theorem relativeDifferentialDesc_fac (φ : O₁ ⟶ O₂)
    {F : SheafOfModules (ringSheaf J O₂)} (D : Der[φ ; F]) :
    (relativeDifferential φ).postcomp (relativeDifferentialDesc φ D).val = D := sorry

/-- A morphism out of `Ω(φ)` is determined by the induced derivation. -/
theorem relativeDifferential_postcomp_injective (φ : O₁ ⟶ O₂)
    {F : SheafOfModules (ringSheaf J O₂)} ⦃f g : Ω(φ) ⟶ F⦄
    (h : (relativeDifferential φ).postcomp f.val =
      (relativeDifferential φ).postcomp g.val) :
    f = g := sorry

/-- The relative-differentials sheaf represents relative derivations into module sheaves. -/
@[stacks 04BL, stacks 08RM "topological-space specialization"]
theorem relativeDifferentials_representsDerivations (φ : O₁ ⟶ O₂)
    (F : SheafOfModules (ringSheaf J O₂)) (D : Der[φ ; F]) :
    ∃! f : Ω(φ) ⟶ F,
      (relativeDifferential φ).postcomp f.val = D := sorry

namespace RelativeDifferentials

/-- Descending the derivation induced by a morphism recovers that morphism. -/
@[simp]
theorem desc_postcomp_relativeDifferential (φ : O₁ ⟶ O₂)
    {F : SheafOfModules (ringSheaf J O₂)}
    (f : Ω(φ) ⟶ F) :
    relativeDifferentialDesc φ
      ((relativeDifferential φ).postcomp f.val) = f := sorry

/-- Morphisms from relative differentials are equivalent to relative derivations. -/
@[stacks 04BL, stacks 08RM "Hom--derivation equivalence"]
noncomputable def homEquiv (φ : O₁ ⟶ O₂)
    (F : SheafOfModules (ringSheaf J O₂)) :
    (Ω(φ) ⟶ F) ≃ Der[φ ; F] where
  toFun f := (relativeDifferential φ).postcomp f.val
  invFun := relativeDifferentialDesc φ
  left_inv := desc_postcomp_relativeDifferential φ
  right_inv := relativeDifferentialDesc_fac φ

/-- The forward map of the representing equivalence is postcomposition with the universal
derivation. -/
@[simp]
theorem homEquiv_apply (φ : O₁ ⟶ O₂)
    {F : SheafOfModules (ringSheaf J O₂)}
    (f : Ω(φ) ⟶ F) :
    homEquiv φ F f = (relativeDifferential φ).postcomp f.val := sorry

/-- The representing equivalence evaluates on a section by applying the target morphism to the
universal differential. -/
@[simp]
theorem homEquiv_apply_d (φ : O₁ ⟶ O₂)
    {F : SheafOfModules (ringSheaf J O₂)}
    (f : Ω(φ) ⟶ F) (X : Cᵒᵖ) (r : O₂.obj.obj X) :
    (homEquiv φ F f).d r =
      f.val.app X (((relativeDifferential φ).app X).d r) := sorry

/-- The inverse map of the representing equivalence is universal descent. -/
@[simp]
theorem homEquiv_symm_apply (φ : O₁ ⟶ O₂)
    {F : SheafOfModules (ringSheaf J O₂)} (D : Der[φ ; F]) :
    (homEquiv φ F).symm D = relativeDifferentialDesc φ D := sorry

/-- The descended morphism has the prescribed value on universal differential generators. -/
@[simp]
theorem homEquiv_symm_apply_d (φ : O₁ ⟶ O₂)
    {F : SheafOfModules (ringSheaf J O₂)} (D : Der[φ ; F])
    (X : Cᵒᵖ) (r : O₂.obj.obj X) :
    ((homEquiv φ F).symm D).val.app X
        (((relativeDifferential φ).app X).d r) = D.d r := sorry

/-- The representing equivalence is natural in the target module sheaf. -/
theorem homEquiv_comp (φ : O₁ ⟶ O₂)
    {F G : SheafOfModules (ringSheaf J O₂)} (g : F ⟶ G)
    (f : Ω(φ) ⟶ F) :
    homEquiv φ G (f ≫ g) =
      (SheafOfModules.RelativeDerivation.functor φ).map g
        (homEquiv φ F f) := sorry

/-- Universal descent commutes with postcomposition in the target module sheaf. -/
@[simp]
theorem relativeDifferentialDesc_postcomp (φ : O₁ ⟶ O₂)
    {F G : SheafOfModules (ringSheaf J O₂)} (D : Der[φ ; F]) (g : F ⟶ G) :
    relativeDifferentialDesc φ (D.postcomp g.val) =
      relativeDifferentialDesc φ D ≫ g := sorry

/-- Relative differentials corepresent the functor of relative derivations. -/
@[stacks 04BL, stacks 08RM "corepresented relative derivations"]
noncomputable def corepresentableBy (φ : O₁ ⟶ O₂) :
    (SheafOfModules.RelativeDerivation.functor φ).CorepresentableBy
      (relativeDifferentials φ) where
  homEquiv := homEquiv φ _
  homEquiv_comp := homEquiv_comp φ

/-- The natural representing isomorphism for relative differentials. -/
@[stacks 04BL, stacks 08RM "representing isomorphism for relative derivations"]
noncomputable def representingIso (φ : O₁ ⟶ O₂) :
    coyoneda.obj (Opposite.op (relativeDifferentials φ)) ≅
      SheafOfModules.RelativeDerivation.functor φ :=
  (corepresentableBy φ).toIso

/-- The forward component of the natural representing isomorphism is postcomposition with the
universal derivation. -/
@[simp]
theorem representingIso_hom_app (φ : O₁ ⟶ O₂)
    (F : SheafOfModules (ringSheaf J O₂))
    (f : Ω(φ) ⟶ F) :
    (representingIso φ).hom.app F f =
      (relativeDifferential φ).postcomp f.val := sorry

/-- The inverse component of the natural representing isomorphism is universal descent. -/
@[simp]
theorem representingIso_inv_app (φ : O₁ ⟶ O₂)
    (F : SheafOfModules (ringSheaf J O₂)) (D : Der[φ ; F]) :
    (representingIso φ).inv.app F D = relativeDifferentialDesc φ D := sorry

end RelativeDifferentials

end SheafOfModules.RingedSite
