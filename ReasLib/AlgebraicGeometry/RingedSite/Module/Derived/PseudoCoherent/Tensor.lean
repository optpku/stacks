/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor

/-!
# Pseudo-coherent derived tensor products on ringed sites

This module records the tensor-stability API at the level of the abstract fixed-right derived
tensor construction.  Concrete models only need to provide a `DerivedTensor.Right.Has` instance;
K-flat resolutions and other construction-specific hypotheses do not leak into consumers.
-/

@[expose] public section

open CategoryTheory
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived)
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

set_option checkBinderAnnotations false

namespace RingedSite.Hom.ModuleDerived

section

variable {X : RingedSite.{u, v, w}}
variable [UnivLE.{max u v, w}]
variable [∀ U : X, HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [MonoidalCategory (ModuleCat.{w} X)] [MonoidalPreadditive (ModuleCat.{w} X)]
variable [∀ (K L : CochainComplex (ModuleCat.{w} X) ℤ),
  HomologicalComplex.HasMapBifunctor K L (curriedTensor (ModuleCat.{w} X)) (up ℤ)]
variable [CategoryTheory.DerivedCategory.DerivedTensor.Right.Has (C := ModuleCat.{w} X)]

/-- Lemma 21.45.5 (1): if `K` is `n`-pseudo-coherent and lies in `D^{≤ a}`, while `L` is
`m`-pseudo-coherent and lies in `D^{≤ b}`, then `K ⊗ᴸ L` is
`max (m + a) (n + b)`-pseudo-coherent. -/
@[stacks 09J9 "(1)"]
theorem IsMPseudoCoherent.tensor
    {K L : ModuleDerived.{w} X} {n m a b : ℤ}
    (hK : K.IsMPseudoCoherent n) (hKLE : K.IsLE a)
    (hL : L.IsMPseudoCoherent m) (hLLE : L.IsLE b) :
    IsMPseudoCoherent (X := X) (K ⊗ᴸ L) (max (m + a) (n + b)) := sorry

/-- Lemma 21.45.5 (2): the fixed-right derived tensor product of two pseudo-coherent objects is
pseudo-coherent. -/
@[stacks 09J9 "(2)"]
theorem IsPseudoCoherent.tensor
    {K L : ModuleDerived.{w} X}
    (hK : K.IsPseudoCoherent) (hL : L.IsPseudoCoherent) :
    IsPseudoCoherent (X := X) (K ⊗ᴸ L) := sorry

end

end RingedSite.Hom.ModuleDerived
