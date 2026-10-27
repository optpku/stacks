/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect

@[expose] public section

/-!
# Pseudo-coherent module complexes on ringed sites

This module owns the representative-based pseudo-coherence predicates for complexes and derived
objects of module sheaves on a bundled ringed site.  The local strict-perfect approximation
criterion is separated into `PseudoCoherent.Local`.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived localizedRestrictionComplex)

noncomputable section

universe u v w

set_option checkBinderAnnotations false

section

variable {X : RingedSite.{u, v, w}}
variable [UnivLE.{max u v, w}]
variable [∀ U : X.carrier,
  HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X.carrier,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

namespace CochainComplex

/-- A complex of `𝒪_X`-modules is `m`-pseudo-coherent if locally it admits a map from a strictly
perfect complex inducing cohomology isomorphisms above `m` and an epimorphism in degree `m`. -/
@[stacks 08FT]
def IsMPseudoCoherent (E : CochainComplex (ModuleCat.{w} X) ℤ) (m : ℤ) : Prop :=
  ∀ U : X.carrier, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
    ∃ E' : CochainComplex (ModuleCat.{w} (X.localization I.Y)) ℤ,
      RingedSite.CochainComplex.IsStrictlyPerfect (X := X.localization I.Y) E' ∧
        ∃ alpha : E' ⟶ (localizedRestrictionComplex.{w} X I.Y).obj E,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap alpha j)) ∧
            Epi (HomologicalComplex.homologyMap alpha m)

/-- A complex of `𝒪_X`-modules is pseudo-coherent if it is `m`-pseudo-coherent for every integer
`m`. -/
@[stacks 08FT]
def IsPseudoCoherent (E : CochainComplex (ModuleCat.{w} X) ℤ) : Prop :=
  ∀ m : ℤ, E.IsMPseudoCoherent m

end CochainComplex

-- Local instance justification (defeq pin): DerivedCategory.Q must use the standard module-sheaf localization fixed by RingedSite.Hom.ModuleDerived.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

namespace RingedSite.Hom.ModuleDerived

open _root_.CochainComplex

/-- An object of `D(𝒪_X)` is `m`-pseudo-coherent when it has an `m`-pseudo-coherent complex
representative. -/
@[stacks 08FT]
def IsMPseudoCoherent (K : ModuleDerived.{w} X) (m : ℤ) : Prop :=
  ∃ E : CochainComplex (ModuleCat.{w} X) ℤ, ∃ _ : K ≅ DerivedCategory.Q.obj E,
    E.IsMPseudoCoherent m

/-- An object of `D(𝒪_X)` is pseudo-coherent when it has a pseudo-coherent complex
representative. -/
@[stacks 08FT]
def IsPseudoCoherent (K : ModuleDerived.{w} X) : Prop :=
  ∃ E : CochainComplex (ModuleCat.{w} X) ℤ, ∃ _ : K ≅ DerivedCategory.Q.obj E,
    E.IsPseudoCoherent

/-- Every complex representing an `m`-pseudo-coherent derived module is `m`-pseudo-coherent. -/
@[stacks 08FU "(2)"]
theorem IsMPseudoCoherent.of_representation
    {K : ModuleDerived.{w} X} {E : CochainComplex (ModuleCat.{w} X) ℤ} {m : ℤ}
    (hK : K.IsMPseudoCoherent m) (e : DerivedCategory.Q.obj E ≅ K) :
    E.IsMPseudoCoherent m := sorry

/-- Every complex representing a pseudo-coherent derived module is pseudo-coherent. -/
theorem IsPseudoCoherent.of_representation
    {K : ModuleDerived.{w} X} {E : CochainComplex (ModuleCat.{w} X) ℤ}
    (hK : K.IsPseudoCoherent) (e : DerivedCategory.Q.obj E ≅ K) :
    E.IsPseudoCoherent := sorry

end RingedSite.Hom.ModuleDerived

namespace CochainComplex

/-- An `m`-pseudo-coherent complex defines an `m`-pseudo-coherent derived module. -/
theorem IsMPseudoCoherent.q_obj
    {E : CochainComplex (ModuleCat.{w} X) ℤ} {m : ℤ}
    (hE : E.IsMPseudoCoherent m) :
    RingedSite.Hom.ModuleDerived.IsMPseudoCoherent (DerivedCategory.Q.obj E) m := sorry

/-- A pseudo-coherent complex defines a pseudo-coherent derived module. -/
theorem IsPseudoCoherent.q_obj
    {E : CochainComplex (ModuleCat.{w} X) ℤ} (hE : E.IsPseudoCoherent) :
    RingedSite.Hom.ModuleDerived.IsPseudoCoherent (DerivedCategory.Q.obj E) := sorry

end CochainComplex

namespace RingedSite.DerivedCategory

open _root_.CochainComplex
open _root_.RingedSite.Hom.ModuleDerived

section

/-- An object is `m`-pseudo-coherent exactly when it has an `m`-pseudo-coherent complex
representative. -/
theorem isMPseudoCoherent_iff_exists_mPseudoCoherent_representative
    (K : ModuleDerived.{w} X) (m : ℤ) :
    K.IsMPseudoCoherent m ↔
      ∃ E : CochainComplex (ModuleCat.{w} X) ℤ, ∃ _ : K ≅ DerivedCategory.Q.obj E,
        E.IsMPseudoCoherent m := sorry

/-- Pseudo-coherence of a derived object unfolds to the existence of a pseudo-coherent complex
representative. -/
theorem isPseudoCoherent_iff_exists_pseudoCoherent_representative
    (K : ModuleDerived.{w} X) :
    K.IsPseudoCoherent ↔
      ∃ E : CochainComplex (ModuleCat.{w} X) ℤ, ∃ _ : K ≅ DerivedCategory.Q.obj E,
        E.IsPseudoCoherent := sorry

/-- A derived object of `D(𝒪_X)` is pseudo-coherent exactly when it is
`m`-pseudo-coherent for every integer `m`. -/
theorem isPseudoCoherent_iff (K : ModuleDerived.{w} X) :
    K.IsPseudoCoherent ↔ ∀ m : ℤ, K.IsMPseudoCoherent m := sorry

end

end RingedSite.DerivedCategory

end
