module

public import ReasLib.AlgebraicGeometry.Scheme.Coproduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Subfamilies of coproducts of schemes

This file owns the canonical inclusion of a subfamily coproduct into the full coproduct.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.Coproduct

/-- The coproduct of the members of `X` whose indices lie in `J`. -/
@[stacks 03DP "coproduct subfamily"]
noncomputable abbrev subfamily {ι : Type u} [Small.{v} ι]
    (X : ι → Scheme.{v}) (J : Set ι) : Scheme.{v} :=
  ∐ fun j : J ↦ X j

/-- The canonical inclusion of a subfamily coproduct into the full coproduct. -/
@[stacks 03DP "inclusion of a subfamily coproduct"]
noncomputable abbrev inclusion {ι : Type u} [Small.{v} ι]
    (X : ι → Scheme.{v}) (J : Set ι) : subfamily X J ⟶ ∐ X :=
  Sigma.map' Subtype.val (fun j ↦ 𝟙 (X j))

/-- Inclusion of a subfamily coproduct is an open immersion. -/
@[stacks 03DP "open immersion of a coproduct subfamily"]
instance inclusion_isOpenImmersion {ι : Type u} [Small.{v} ι]
    (X : ι → Scheme.{v}) (J : Set ι) : IsOpenImmersion (inclusion X J) := sorry

/-- A subfamily summand maps to the corresponding summand of the full coproduct. -/
@[simp, reassoc, stacks 03DP "coproduct subfamily inclusion component"]
theorem ι_inclusion {ι : Type u} [Small.{v} ι]
    (X : ι → Scheme.{v}) (J : Set ι) (j : J) :
    Sigma.ι (fun t : J ↦ X t) j ≫ inclusion X J = Sigma.ι X j.1 := sorry

/-- The summands met by a morphism into a coproduct of schemes. -/
@[stacks 03DP "support in a coproduct"]
def support {ι : Type u} [Small.{v} ι] (X : ι → Scheme.{v})
    {Y : Scheme.{v}} (f : Y ⟶ ∐ X) : Set ι :=
  {i | ∃ y : Y, f.base y ∈ Set.range (Sigma.ι X i).base}

/-- An index belongs to the support exactly when the image meets that summand. -/
@[stacks 03DP "coproduct support membership"]
theorem mem_support_iff {ι : Type u} [Small.{v} ι] (X : ι → Scheme.{v})
    {Y : Scheme.{v}} (f : Y ⟶ ∐ X) (i : ι) :
    i ∈ support X f ↔
      ∃ y : Y, f.base y ∈ Set.range (Sigma.ι X i).base := sorry

/-- Bundled-open form of membership in coproduct support. -/
@[stacks 03DP "coproduct support membership by open range"]
theorem mem_support_iff_opensRange {ι : Type u} [Small.{v} ι]
    (X : ι → Scheme.{v}) {Y : Scheme.{v}} (f : Y ⟶ ∐ X) (i : ι) :
    i ∈ support X f ↔ ∃ y : Y, f.base y ∈ (Sigma.ι X i).opensRange := sorry

/-- Precomposition by a morphism surjective on points does not change coproduct support. -/
@[stacks 03DP "coproduct support under surjective precomposition"]
theorem support_comp_of_surjective {ι : Type u} [Small.{v} ι]
    (X : ι → Scheme.{v}) {Y Z : Scheme.{v}} (g : Z ⟶ Y) (f : Y ⟶ ∐ X)
    (h_surjective : Function.Surjective g.base) :
    support X (g ≫ f) = support X f := sorry

/-- Replacing the source by an isomorphic scheme does not change coproduct support. -/
@[simp, stacks 03DP "coproduct support under source isomorphism"]
theorem support_iso_hom {ι : Type u} [Small.{v} ι]
    (X : ι → Scheme.{v}) {Y Z : Scheme.{v}} (e : Z ≅ Y) (f : Y ⟶ ∐ X) :
    support X (e.hom ≫ f) = support X f := sorry

end AlgebraicGeometry.Scheme.Coproduct
