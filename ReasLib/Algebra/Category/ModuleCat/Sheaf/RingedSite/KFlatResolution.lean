module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.QuasiIso
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.TermwiseFlat.BoundedAbove
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.TermwiseFlat.QuasiIso

/-!
# K-flat resolutions on a ringed site

Complexes of modules over a commutative ring sheaf admit termwise epimorphic K-flat resolutions
with flat terms.  The final declaration connects this geometric existence theorem to the generic
localizer-resolution interface used by monoidal derived localization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite.KFlat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}
variable [UnivLE.{max u v, z}]

variable [Abelian (ringedSiteModuleCategory.{u, v, z, w} J O)]
variable [CategoryWithHomology (ringedSiteModuleCategory.{u, v, z, w} J O)]
variable [MonoidalCategory (ringedSiteModuleCategory.{u, v, z, w} J O)]
variable [MonoidalPreadditive (ringedSiteModuleCategory.{u, v, z, w} J O)]

/-- Every complex of modules on a ringed site admits a termwise epimorphic quasi-isomorphism
from a K-flat, termwise-flat complex. -/
@[stacks 06YS "termwise epimorphic K-flat resolution"]
theorem exists_termwiseEpi_resolution
    (G : CochainComplex (ringedSiteModuleCategory.{u, v, z, w} J O) ℤ) :
    ∃ (K : CochainComplex (ringedSiteModuleCategory.{u, v, z, w} J O) ℤ) (f : K ⟶ G),
      K.IsKFlat ∧ HomologicalComplex.IsTermwiseFlat K ∧ QuasiIso f ∧
        ∀ n : ℤ, Epi (f.f n) := sorry

/-- Every complex of modules on a ringed site admits an epimorphic quasi-isomorphism from a
K-flat, termwise-flat complex. -/
theorem exists_epi_resolution
    (G : CochainComplex (ringedSiteModuleCategory.{u, v, z, w} J O) ℤ) :
    ∃ (K : CochainComplex (ringedSiteModuleCategory.{u, v, z, w} J O) ℤ) (f : K ⟶ G),
      K.IsKFlat ∧ HomologicalComplex.IsTermwiseFlat K ∧ QuasiIso f ∧ Epi f := sorry

/-- Modules on a ringed site have resolutions by K-flat complexes with flat terms, in the
canonical localizer-morphism sense.  Unlike the coarser `KFlat.HasResolutions` instance, this
owner retains the termwise-flat condition needed by pullback arguments. -/
@[stacks 06YS "K-flat termwise-flat resolutions"]
theorem termwiseFlatHasResolutions :
    HomotopyCategory.KFlat.TermwiseFlat.HasResolutions
      (ringedSiteModuleCategory.{u, v, z, w} J O) := sorry

/-- Modules on a ringed site have K-flat resolutions in the canonical localizer sense. -/
@[stacks 0FPB "ringed-site K-flat resolutions"]
instance hasResolutions :
    HomotopyCategory.KFlat.HasResolutions
      (ringedSiteModuleCategory.{u, v, z, w} J O) := sorry

namespace TermwiseFlat

/-- A bounded-above homotopy complex of modules with flat terms belongs to the canonical
subcategory of K-flat termwise-flat models. -/
@[stacks 06YQ "ringed-site bounded-above good models"]
theorem of_boundedAbove
    {K : HomotopyCategory (ringedSiteModuleCategory.{u, v, z, w} J O)
      (ComplexShape.up ℤ)}
    (hFlat : HomologicalComplex.IsTermwiseFlat K.as)
    (hbounded : CochainComplex.minus
      (ringedSiteModuleCategory.{u, v, z, w} J O) K.as) :
    HomotopyCategory.KFlat.termwiseFlat
      (ringedSiteModuleCategory.{u, v, z, w} J O) K := sorry

end TermwiseFlat

end SheafOfModules.RingedSite.KFlat
