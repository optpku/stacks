module

public import ReasLib.CategoryTheory.Successive
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
public import ReasLib.CategoryTheory.Monoidal.Flat

/-!
# Scalar extension and flat lifts of successive module sheaves

Successor maps of module sheaves need not square to zero before scalar extension.
A bounded-above flat successive family admits a compatible flat lift whose scalar
extension is quasi-isomorphic to the given cohomologically bounded-above complex.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite.Successive

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- A successive family of module sheaves is termwise flat if every term is flat. -/
def IsTermwiseFlat {𝒪 : Sheaf J CommRingCat.{u}}
    (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪)) : Prop :=
  ∀ n, CategoryTheory.MonoidalCategory.IsFlat (G.X n)

/-- Termwise flatness is equivalent to flatness in every degree. -/
theorem isTermwiseFlat_iff {𝒪 : Sheaf J CommRingCat.{u}}
    (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪)) :
    IsTermwiseFlat G ↔ ∀ n, CategoryTheory.MonoidalCategory.IsFlat (G.X n) := sorry

variable {𝒪 𝒪₀ : Sheaf J CommRingCat.{u}} (π : 𝒪 ⟶ 𝒪₀)

/-- Degreewise extension of scalars of a successive family along a ring-sheaf morphism. -/
def extend (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪)) :
    CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪₀) :=
  G.map (ChangeOfRings.extendScalars (ringSheafMap.{u, u, u} π))

/-- The terms of the extended family are the scalar extensions of the original terms. -/
theorem extend_X (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
    (n : ℤ) :
    (extend π G).X n = (ChangeOfRings.extendScalars (ringSheafMap.{u, u, u} π)).obj (G.X n) := sorry

/-- The successor maps of the extended family are the scalar extensions of the original maps. -/
theorem extend_d (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
    (n : ℤ) :
    (extend π G).d n = (ChangeOfRings.extendScalars (ringSheafMap.{u, u, u} π)).map (G.d n) := sorry

/-- The canonical adjunct of a map from a module sheaf into a restricted complex term. -/
def adjunct (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
    (K₀ : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J 𝒪₀) ℤ)
    (φ : ∀ n, G.X n ⟶ (restrictionAlong π).obj (K₀.X n)) (n : ℤ) :
    (ChangeOfRings.extendScalars (ringSheafMap.{u, u, u} π)).obj (G.X n) ⟶ K₀.X n :=
  (ChangeOfRings.extendRestrictHomEquiv (ringSheafMap.{u, u, u} π) (G.X n) (K₀.X n)).symm (φ n)

/-- The adjunct is computed by the inverse extension-restriction Hom equivalence. -/
theorem adjunct_spec (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
    (K₀ : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J 𝒪₀) ℤ)
    (φ : ∀ n, G.X n ⟶ (restrictionAlong π).obj (K₀.X n)) (n : ℤ) :
    adjunct π G K₀ φ n =
      (ChangeOfRings.extendRestrictHomEquiv (ringSheafMap.{u, u, u} π)
        (G.X n) (K₀.X n)).symm (φ n) := sorry

/-- Composing the restricted adjunct with the adjunction unit recovers the original map. -/
theorem adjunct_apply (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
    (K₀ : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J 𝒪₀) ℤ)
    (φ : ∀ n, G.X n ⟶ (restrictionAlong π).obj (K₀.X n)) (n : ℤ) :
    (ChangeOfRings.extendRestrictAdjunction (ringSheafMap.{u, u, u} π)).unit.app (G.X n) ≫
      (restrictionAlong π).map (adjunct π G K₀ φ n) = φ n := sorry

/-- Scalar extension makes the successor maps square to zero and the adjuncts a chain map. -/
structure IsChainMapAfterExtend
    (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
    (K₀ : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J 𝒪₀) ℤ)
    (φ : ∀ n, G.X n ⟶ (restrictionAlong π).obj (K₀.X n)) : Prop where
  /-- Successor maps square to zero after extension of scalars. -/
  d_comp_d : ∀ n, (extend π G).d n ≫ (extend π G).d (n + 1) = 0
  /-- Adjuncts commute with the differentials of the target complex. -/
  comm : ∀ n, adjunct π G K₀ φ n ≫ K₀.d n (n + 1) =
    (extend π G).d n ≫ adjunct π G K₀ φ (n + 1)

/-- Square-zero successor maps and commuting adjuncts give compatibility after scalar extension. -/
def IsChainMapAfterExtend.ofMaps
    (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
    (K₀ : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J 𝒪₀) ℤ)
    (φ : ∀ n, G.X n ⟶ (restrictionAlong π).obj (K₀.X n))
    (d_comp_d : ∀ n, (extend π G).d n ≫ (extend π G).d (n + 1) = 0)
    (comm : ∀ n, adjunct π G K₀ φ n ≫ K₀.d n (n + 1) =
      (extend π G).d n ≫ adjunct π G K₀ φ (n + 1)) :
    IsChainMapAfterExtend π G K₀ φ where
  d_comp_d := d_comp_d
  comm := comm

/-- Compatibility after scalar extension is equivalent to square-zero and chain-map conditions. -/
theorem isChainMapAfterExtend_iff
    (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
    (K₀ : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J 𝒪₀) ℤ)
    (φ : ∀ n, G.X n ⟶ (restrictionAlong π).obj (K₀.X n)) :
    IsChainMapAfterExtend π G K₀ φ ↔
      (∀ n, (extend π G).d n ≫ (extend π G).d (n + 1) = 0) ∧
        ∀ n, adjunct π G K₀ φ n ≫ K₀.d n (n + 1) =
          (extend π G).d n ≫ adjunct π G K₀ φ (n + 1) := sorry

/-- Compatible adjuncts commute with the differentials of the associated cochain complex. -/
theorem homAfterExtend_comm
    (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
    (K₀ : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J 𝒪₀) ℤ)
    (φ : ∀ n, G.X n ⟶ (restrictionAlong π).obj (K₀.X n))
    (h : IsChainMapAfterExtend π G K₀ φ) (n : ℤ) :
    adjunct π G K₀ φ n ≫ K₀.d n (n + 1) =
      ((extend π G).toCochainComplex h.d_comp_d).d n (n + 1) ≫
        adjunct π G K₀ φ (n + 1) := sorry

/-- The cochain map from the scalar-extended family with the canonical adjuncts as components. -/
def homAfterExtend
    (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
    (K₀ : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J 𝒪₀) ℤ)
    (φ : ∀ n, G.X n ⟶ (restrictionAlong π).obj (K₀.X n))
    (h : IsChainMapAfterExtend π G K₀ φ) :
    (extend π G).toCochainComplex h.d_comp_d ⟶ K₀ :=
  CochainComplex.ofHom (adjunct π G K₀ φ) (homAfterExtend_comm π G K₀ φ h)

/-- The components of the induced cochain map are the canonical adjuncts. -/
theorem homAfterExtend_f
    (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
    (K₀ : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J 𝒪₀) ℤ)
    (φ : ∀ n, G.X n ⟶ (restrictionAlong π).obj (K₀.X n))
    (h : IsChainMapAfterExtend π G K₀ φ) (n : ℤ) :
    (homAfterExtend π G K₀ φ h).f n = adjunct π G K₀ φ n := sorry

/-- A bounded-above flat successive family compatible with a cohomologically bounded-above
complex after a locally surjective ring-sheaf morphism factors through a bounded-above flat
successive family whose scalar extension maps quasi-isomorphically to that complex. -/
@[stacks 0DIT]
theorem existsFlatLift (π : 𝒪 ⟶ 𝒪₀) [Sheaf.IsLocallySurjective π]
    (G : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
    (hGflat : IsTermwiseFlat G) (hGzero : ∃ N, G.IsStrictlyLE N)
    (K₀ : CochainComplex (ringedSiteModuleCategory.{u, u, u, u} J 𝒪₀) ℤ)
    (hK : ∃ N, K₀.IsLE N)
    (φ : ∀ n, G.X n ⟶ (restrictionAlong π).obj (K₀.X n))
    (hφ : IsChainMapAfterExtend π G K₀ φ) :
    ∃ (F : CategoryTheory.Successive (ringedSiteModuleCategory.{u, u, u, u} J 𝒪))
      (ι : CategoryTheory.Successive.Hom G F)
      (ψ : ∀ n, F.X n ⟶ (restrictionAlong π).obj (K₀.X n))
      (hψ : IsChainMapAfterExtend π F K₀ ψ),
      IsTermwiseFlat F ∧
        (∃ N, F.IsStrictlyLE N) ∧
        (∀ n, ι.f n ≫ ψ n = φ n) ∧
        QuasiIso (homAfterExtend π F K₀ ψ hψ) := sorry

end SheafOfModules.RingedSite.Successive
