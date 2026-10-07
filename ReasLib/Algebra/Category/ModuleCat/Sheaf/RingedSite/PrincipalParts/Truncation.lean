module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts.Truncation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.Construction

/-!
# Truncation of principal-parts sheaves

The objectwise transition `PresheafOfModules.PrincipalParts.truncate φ F h` for `h : k ≤ l`
sheafifies to a canonical morphism between principal-parts sheaves. These transitions are
functorial in the module sheaf and recover the universal differential operator of order `k` from
the one of order `l`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.PrincipalParts

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}

/-- Tag 0G3T: the canonical truncation morphism from principal parts of order `l` to
principal parts of order `k` for `k ≤ l`. -/
@[stacks 0G3T "sheaf order truncation"]
noncomputable def truncate (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) {k l : ℕ} (h : k ≤ l) :
    sheaf phi F l ⟶ sheaf phi F k :=
  (moduleSheafification O₂).map
    (PresheafOfModules.PrincipalParts.truncate phi.hom F.val h)

/-- Under exact sheafification, every truncation morphism of principal-parts sheaves is an
epimorphism. -/
instance truncate_epi [HasSheafify J AddCommGrpCat.{max u v}]
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂)
    {k l : ℕ} (h : k ≤ l) : Epi (truncate phi F h) := sorry

/-- Sheaf truncation along a reflexive order comparison is the identity. -/
@[simp]
theorem truncate_refl (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) (k : ℕ) :
    truncate phi F (le_refl k) = 𝟙 (sheaf phi F k) := sorry

/-- Successive sheaf truncations equal truncation along the composite order comparison. -/
@[simp]
theorem truncate_trans (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) {k l n : ℕ}
    (hkl : k ≤ l) (hln : l ≤ n) :
    truncate phi F hln ≫ truncate phi F hkl =
      truncate phi F (hkl.trans hln) := sorry

section Naturality

variable {F G : ringedSiteModuleCategory J O₂}

/-- Sheaf truncation is natural with respect to morphisms of module sheaves. -/
theorem truncate_naturality (phi : O₁ ⟶ O₂) {k l : ℕ}
    (h : k ≤ l) (alpha : F ⟶ G) :
    map phi l alpha ≫ truncate phi G h =
      truncate phi F h ≫ map phi k alpha := sorry

end Naturality

/-- Truncation in the order bound is a natural transformation between principal-parts
endofunctors on module sheaves. -/
noncomputable def truncateNatTrans (phi : O₁ ⟶ O₂) {k l : ℕ} (h : k ≤ l) :
    functor phi l ⟶ functor phi k where
  app F := truncate phi F h
  naturality {_ _} alpha := truncate_naturality phi h alpha

/-- Postcomposing the universal order-`l` differential operator with truncation recovers the
universal order-`k` differential operator. -/
@[simp]
theorem truncate_fac (phi : O₁ ⟶ O₂)
    (F : ringedSiteModuleCategory J O₂) {k l : ℕ} (h : k ≤ l) :
    universalOperator (corepresentation phi F l) ≫
        (restrictionAlong phi).map (truncate phi F h) =
      universalOperator (corepresentation phi F k) := sorry

end SheafOfModules.RingedSite.PrincipalParts
