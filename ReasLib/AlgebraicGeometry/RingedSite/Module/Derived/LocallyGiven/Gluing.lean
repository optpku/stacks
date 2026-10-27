/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocallyGiven.Simplicial
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Basis
public import ReasLib.CategoryTheory.Sites.MorphismOfSites

/-!
# Gluing uniformly bounded below locally given derived modules

Local derived modules indexed by a full subcategory covering an auxiliary site
glue uniquely when negative self-Exts vanish and cohomology has a uniform lower
bound. Compatibility of global isomorphisms is expressed by their restrictions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite RingedSite.Hom
open RingedSite.ModuleDerived

noncomputable section

universe u v w uB vB

namespace RingedSite.ModuleDerived

variable {X : RingedSite.{u, v, w}}
variable {B : Type uB} [Category.{vB} B]
variable [UnivLE.{max u v, w}]
variable {D : LocallyGiven.{u, v, w, w, uB, vB} X B}

namespace Solution

/-- An isomorphism of global objects is compatible with two solutions when its
restrictions intertwine the identifications `ρ_U`. -/
abbrev IsCompatibleIso (S S' : Solution D) (e : S.obj ≅ S'.obj) : Prop :=
  ∀ U : B,
    (localizedRestrictionDerived.{w} X (D.u.obj U)).map e.hom ≫ (S'.iso U).hom =
      (S.iso U).hom

/-- Equational form of compatibility of an isomorphism between solutions. -/
theorem IsCompatibleIso.w {S S' : Solution D} {e : S.obj ≅ S'.obj}
    (h : IsCompatibleIso S S' e) (U : B) :
    (localizedRestrictionDerived.{w} X (D.u.obj U)).map e.hom ≫ (S'.iso U).hom =
      (S.iso U).hom :=
  sorry

end Solution

namespace LocallyGiven

/-- A locally given datum is uniformly bounded below when there is a single
integer `t` such that `(DerivedCategory.homologyFunctor _ i).obj (D.obj U)` is
zero for all `U : B` and all `i < t`. -/
def uniformlyBoundedBelow (D : LocallyGiven.{u, v, w, w, uB, vB} X B) : Prop :=
  ∃ t : ℤ, ∀ (U : B) (i : ℤ), i < t →
    IsZero ((DerivedCategory.homologyFunctor _ i).obj (D.obj U))

/-- Unfolding of uniform boundedness below. -/
theorem uniformlyBoundedBelow_iff (D : LocallyGiven.{u, v, w, w, uB, vB} X B) :
    uniformlyBoundedBelow D ↔
      ∃ t : ℤ, ∀ (U : B) (i : ℤ), i < t →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj (D.obj U)) :=
  sorry

end LocallyGiven

end RingedSite.ModuleDerived

universe ιfam u' v'

open scoped SemiRepresentableFamily

namespace RingedSite.ModuleDerived.LocallyGiven

variable {X : RingedSite.{u, v, w}}
variable [h_eqX : HasEqualizers X.carrier] [h_pbX : HasPullbacks X.carrier]
variable {B : Type uB} [Category.{vB} B]
variable [h_univLE : UnivLE.{max u v, w}]
variable (D : LocallyGiven.{u, v, w, w, uB, vB} X B)
variable {C' : Type u'} [Category.{v'} C']
variable [h_eqC : HasEqualizers C'] [h_pbC : HasPullbacks C']
variable (J' : GrothendieckTopology C') (u' : C' ⥤ X)
variable [h_sites : IsMorphismOfSites J' X.siteTopology u']
variable [h_eqPres : PreservesLimitsOfShape WalkingParallelPair u']
variable [h_pbPres : PreservesLimitsOfShape WalkingCospan u']
variable (ι : B ⥤ C') [h_full : ι.Full] [h_faithful : ι.Faithful]
include h_eqX h_pbX h_eqC h_pbC h_sites h_eqPres h_pbPres h_full h_faithful

/-- Locally given derived modules with vanishing negative self-Exts and a uniform
lower cohomological bound admit a global solution when their indexing category
embeds fully faithfully as a covering basis in an auxiliary site whose functor
to the ringed site defines a morphism of sites and preserves equalizers and
pullbacks, with both sites admitting these limits. -/
@[stacks 0DCB]
theorem exists_solution
    (h_restrict : D.u = ι ⋙ u')
    (h_cover : ∀ W : C', ∃ 𝒰 : FormalCoproduct.{ιfam} (Over W),
      𝒰.IsBasisCovering J'.toPrecoverage (Set.range ι.obj))
    (h_neg : negativeSelfExt h_univLE D)
    (h_bound : uniformlyBoundedBelow D) :
    Nonempty (Solution D) :=
  sorry

/-- Any two solutions of uniformly bounded below locally given derived modules
with vanishing negative self-Exts admit a unique compatible isomorphism when the
indexing category embeds fully faithfully as a covering basis in an auxiliary
site whose functor to the ringed site defines a morphism of sites and preserves
equalizers and pullbacks, with both sites admitting these limits. -/
@[stacks 0DCB]
theorem unique_hom_solution
    (h_restrict : D.u = ι ⋙ u')
    (h_cover : ∀ W : C', ∃ 𝒰 : FormalCoproduct.{ιfam} (Over W),
      𝒰.IsBasisCovering J'.toPrecoverage (Set.range ι.obj))
    (h_neg : negativeSelfExt h_univLE D)
    (h_bound : uniformlyBoundedBelow D)
    (S S' : Solution D) :
    ∃ e : S.obj ≅ S'.obj,
      Solution.IsCompatibleIso S S' e ∧
        ∀ e' : S.obj ≅ S'.obj, Solution.IsCompatibleIso S S' e' → e'.hom = e.hom :=
  sorry

end RingedSite.ModuleDerived.LocallyGiven
