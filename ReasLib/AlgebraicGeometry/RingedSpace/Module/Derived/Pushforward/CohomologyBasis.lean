module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RHom.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.Ext
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basis-local criteria for derived pushforward cohomology

Negative cohomology vanishing is recorded first as a reusable predicate on the canonical preimage
cohomology presheaf.  The internal-Hom specialization is a separate bridge, so the cohomological
local-to-global API does not require a closed monoidal structure.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Pushforward.CohomologyBasis

variable {X Y : RingedSpace.{u}}

/-- Basiswise vanishing in every negative degree for hypercohomology over inverse-image opens. -/
@[stacks 0D66 "basiswise negative preimage cohomology vanishing"]
def Negative (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (K : ModuleDerived X) : Prop :=
  ∀ ⦃V : Opens Y.carrier⦄, V ∈ 𝓑 → ∀ i : ℤ, i < 0 →
    IsZero (moduleOpenHypercohomology X (preimageOpen f V) K i)

/-- The basiswise hypercohomology hypothesis also vanishes objectwise in the canonical preimage
cohomology presheaf model. -/
@[stacks 0D66 "basiswise preimage cohomology presheaf vanishing"]
theorem Negative.presheafObjIsZero
    {f : X ⟶ Y} {𝓑 : Set (Opens Y.carrier)} {K : ModuleDerived X}
    (hK : Negative f 𝓑 K) {V : Opens Y.carrier} (hV : V ∈ 𝓑)
    (i : ℤ) (hi : i < 0) :
    IsZero ((Pushforward.Cohomology.preimagePresheaf f K i).obj (op V)) := sorry

/-- Stacks 0D66 (1): basiswise negative preimage cohomology forces the negative cohomology
objects of the derived pushforward to vanish. -/
@[stacks 0D66 "negative cohomology of a derived pushforward"]
theorem Negative.pushforwardIsZero
    {f : X ⟶ Y} {𝓑 : Set (Opens Y.carrier)} {K : ModuleDerived X}
    (hK : Negative f 𝓑 K) (h𝓑 : Opens.IsBasis 𝓑) (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((moduleDerivedPushforward f).obj K)) := sorry

/-- Under the same hypothesis, the underlying additive negative cohomology sheaf of the derived
pushforward is zero. -/
@[stacks 0D66 "underlying negative cohomology sheaf of a derived pushforward"]
theorem Negative.underlyingPushforwardIsZero
    {f : X ⟶ Y} {𝓑 : Set (Opens Y.carrier)} {K : ModuleDerived X}
    (hK : Negative f 𝓑 K) (h𝓑 : Opens.IsBasis 𝓑) (i : ℤ) (hi : i < 0) :
    IsZero (RingedSite.Hom.ModuleDerived.underlyingCohomologySheaf Y.opensRingedSite
      ((moduleDerivedPushforward f).obj K) i) := sorry

/-- Stacks 0D66 (2): basiswise negative vanishing extends to every open subset. -/
@[stacks 0D66 "negative preimage cohomology on every open"]
theorem Negative.allOpens
    {f : X ⟶ Y} {𝓑 : Set (Opens Y.carrier)} {K : ModuleDerived X}
    (hK : Negative f 𝓑 K) (h𝓑 : Opens.IsBasis 𝓑)
    (V : Opens Y.carrier) (i : ℤ) (hi : i < 0) :
    IsZero (moduleOpenHypercohomology X (preimageOpen f V) K i) := sorry

/-- Presheaf-model companion to `Negative.allOpens`. -/
@[stacks 0D66 "negative preimage cohomology presheaf on every open"]
theorem Negative.presheafAllOpens
    {f : X ⟶ Y} {𝓑 : Set (Opens Y.carrier)} {K : ModuleDerived X}
    (hK : Negative f 𝓑 K) (h𝓑 : Opens.IsBasis 𝓑)
    (V : Opens Y.carrier) (i : ℤ) (hi : i < 0) :
    IsZero ((Pushforward.Cohomology.preimagePresheaf f K i).obj (op V)) := sorry

/-- Stacks 0D66 (3): degree-zero preimage cohomology is already a sheaf when negative cohomology
vanishes on a basis. -/
@[stacks 0D66 "sheafness of degree-zero preimage cohomology"]
theorem Negative.zeroIsSheaf
    {f : X ⟶ Y} {𝓑 : Set (Opens Y.carrier)} {K : ModuleDerived X}
    (hK : Negative f 𝓑 K) (h𝓑 : Opens.IsBasis 𝓑) :
    Presheaf.IsSheaf (Opens.grothendieckTopology Y.carrier)
      (Pushforward.Cohomology.preimagePresheaf f K 0) := sorry

/-- Basiswise vanishing of negative shifted morphisms after canonical derived restriction to the
inverse-image opens. -/
@[stacks 0D66 "basiswise negative Ext vanishing on inverse-image opens"]
def NegativeExt (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier))
    (K L : ModuleDerived X) : Prop :=
  ∀ ⦃V : Opens Y.carrier⦄, V ∈ 𝓑 → ∀ i : ℤ, i < 0 →
    IsZero (AddCommGrpCat.of
      (Ext⁽i⁾((moduleRestrictionToOpenDerived X (preimageOpen f V)).obj K,
        (moduleRestrictionToOpenDerived X (preimageOpen f V)).obj L)))

/-- Chosen restricted-complex representatives give the same basiswise negative Ext condition as
canonical derived restriction. -/
@[stacks 0D66 "negative Ext for restricted representatives"]
theorem NegativeExt.iffRepresentative
    (f : X ⟶ Y) (𝓑 : Set (Opens Y.carrier)) (K L : ModuleDerived X) :
    NegativeExt f 𝓑 K L ↔
      ∀ ⦃V : Opens Y.carrier⦄, V ∈ 𝓑 → ∀ i : ℤ, i < 0 →
        IsZero (AddCommGrpCat.of
          (Ext⁽i⁾(restrictedModuleDerivedOnOpen X (preimageOpen f V) K,
            restrictedModuleDerivedOnOpen X (preimageOpen f V) L))) := sorry

/-- Stacks 0D66 (4): basiswise negative Ext vanishing extends to every inverse-image open. -/
@[stacks 0D66 "negative Ext vanishing on every inverse-image open"]
theorem NegativeExt.allOpens
    {f : X ⟶ Y} {𝓑 : Set (Opens Y.carrier)} {K L : ModuleDerived X}
    (hKL : NegativeExt f 𝓑 K L) (h𝓑 : Opens.IsBasis 𝓑)
    (V : Opens Y.carrier) (i : ℤ) (hi : i < 0) :
    IsZero (AddCommGrpCat.of
      (Ext⁽i⁾((moduleRestrictionToOpenDerived X (preimageOpen f V)).obj K,
        (moduleRestrictionToOpenDerived X (preimageOpen f V)).obj L))) := sorry

/-- Negative local Ext vanishing is the negative preimage-cohomology condition for the derived
internal Hom. -/
@[stacks 0D66 "negative Ext as negative internal-Hom cohomology"]
theorem NegativeExt.toInternalHom
    [MonoidalCategory (ModuleDerived X)] [MonoidalClosed (ModuleDerived X)]
    {f : X ⟶ Y} {𝓑 : Set (Opens Y.carrier)} {K L : ModuleDerived X}
    (hKL : NegativeExt f 𝓑 K L) : Negative f 𝓑 (K ⟹ L) := sorry

/-- Stacks 0D66 (5): the degree-zero preimage internal-Hom presheaf is a sheaf under basiswise
negative Ext vanishing. -/
@[stacks 0D66 "sheafness of the local derived-Hom presheaf"]
theorem NegativeExt.zeroInternalHomIsSheaf
    [MonoidalCategory (ModuleDerived X)] [MonoidalClosed (ModuleDerived X)]
    {f : X ⟶ Y} {𝓑 : Set (Opens Y.carrier)} {K L : ModuleDerived X}
    (hKL : NegativeExt f 𝓑 K L) (h𝓑 : Opens.IsBasis 𝓑) :
    Presheaf.IsSheaf (Opens.grothendieckTopology Y.carrier)
      (Pushforward.Cohomology.preimagePresheaf f (K ⟹ L) 0) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Pushforward.CohomologyBasis

end
