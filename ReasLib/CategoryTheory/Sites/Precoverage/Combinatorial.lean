/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Precoverage.Comparison

/-!
# Precoverages compared by combinatorial covering families

This leaf expresses the source-facing operation of replacing every cover in an
ambient precoverage by a combinatorially equivalent cover from a sub-precoverage.
It is independent of a chosen pretopology or coverage presentation.
-/

@[expose] public section

universe u v w

namespace CategoryTheory.Precoverage

variable {C : Type u} [Category.{v} C]

/-- Every cover of `K` can be replaced by a combinatorially equivalent cover
of `L`.  Families use the site-index universe, which suffices to present every
presieve on `C`. -/
def coversUpToCombinatorialEquivalence (K L : Precoverage C) : Prop :=
  K.coversUpTo L fun {_} 𝒰 𝒱 ↦
    SemiRepresentableFamily.Over.CombinatoriallyEquivalent 𝒰 𝒱

/-- Replacing every cover by a combinatorially equivalent cover induces an
inclusion of the generated Grothendieck topologies. -/
theorem toGrothendieck_le_of_combinatorial_covers
    {K L : Precoverage C} (h : K.coversUpToCombinatorialEquivalence L) :
    K.toGrothendieck ≤ L.toGrothendieck := sorry

/-- A set-valued sheaf for `L` is a sheaf for `K` when every `K`-cover can be
replaced by a combinatorially equivalent `L`-cover. -/
theorem isSheaf_of_combinatorial_covers
    {K L : Precoverage C} {P : Cᵒᵖ ⥤ Type w}
    (h : K.coversUpToCombinatorialEquivalence L)
    (hP : Presheaf.IsSheaf L.toGrothendieck P) :
    Presheaf.IsSheaf K.toGrothendieck P := sorry

/-- Mutual combinatorial replacement of covers gives equivalent set-valued
sheaf conditions. -/
theorem isSheaf_iff_of_mutual_combinatorial_covers
    {K L : Precoverage C} {P : Cᵒᵖ ⥤ Type w}
    (hKL : K.coversUpToCombinatorialEquivalence L)
    (hLK : L.coversUpToCombinatorialEquivalence K) :
    Presheaf.IsSheaf K.toGrothendieck P ↔
      Presheaf.IsSheaf L.toGrothendieck P := sorry

/-- Two sub-precoverages of one ambient precoverage generate the same topology
when every ambient cover can be replaced combinatorially by a cover from either
sub-precoverage. -/
theorem toGrothendieck_eq_of_common_ambient_covers
    {K K₁ K₂ : Precoverage C} (h₁ : K₁ ≤ K) (h₂ : K₂ ≤ K)
    (hK₁ : K.coversUpToCombinatorialEquivalence K₁)
    (hK₂ : K.coversUpToCombinatorialEquivalence K₂) :
    K₁.toGrothendieck = K₂.toGrothendieck := sorry

/-- Under common ambient combinatorial cover replacement, a set-valued
presheaf is a sheaf for one sub-precoverage exactly when it is a sheaf for the
other. -/
theorem isSheaf_iff_of_common_ambient_covers
    {K K₁ K₂ : Precoverage C} {P : Cᵒᵖ ⥤ Type w}
    (h₁ : K₁ ≤ K) (h₂ : K₂ ≤ K)
    (hK₁ : K.coversUpToCombinatorialEquivalence K₁)
    (hK₂ : K.coversUpToCombinatorialEquivalence K₂) :
    Presheaf.IsSheaf K₁.toGrothendieck P ↔
      Presheaf.IsSheaf K₂.toGrothendieck P := sorry

end CategoryTheory.Precoverage
