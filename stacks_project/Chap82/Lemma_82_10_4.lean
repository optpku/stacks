/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_30_3
public import stacks_project.Chap82.Lemma_82_10_4_Pullback

/-!
# Composition of flat pullbacks of cycles

In Situation 82.2.1, a composable pair of flat morphisms of good algebraic
spaces of relative dimensions `r` and `s` has composite of relative dimension
`r + s`, and successive flat pullbacks of cycles agree with pullback along the
composite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 82.10.4 (1): In Situation 82.2.1, if `f : X ⟶ Y` and `g : Y ⟶ Z` are
flat of relative dimensions `r` and `s`, then `f ≫ g` is flat of relative
dimension `r + s`. Flatness of the composite is `flat_comp`; this instance
records the relative-dimension additivity. -/
@[stacks 0EPA]
instance instRelativeDimension_comp_of_flat {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : ℕ)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [Flat f] [RelativeDimension f r] [RelativeDimension g s] :
    RelativeDimension (f ≫ g) (r + s) :=
  sorry

namespace Hom

/-- Lemma 82.10.4 (2): In Situation 82.2.1 let `X`, `Y`, `Z / B` be good. Let
`f : X ⟶ Y` and `g : Y ⟶ Z` be flat morphisms of relative dimensions `r` and
`s` over `B`. Then `f^* ∘ g^* = (g ∘ f)^*` as maps of cycles
`Z_k(Z) → Z_{k + r + s}(X)`. -/
@[stacks 0EPA]
theorem flatPullback_comp {S : Scheme.{u}} {B X Y Z : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pZ : Z ⟶ B) [QuasiSeparated pZ] [LocallyOfFiniteType pZ]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [LocallyOfFiniteType f] [Flat f] [RelativeDimension f r]
    (g : Y ⟶ Z) (s : ℕ) [LocallyOfFiniteType g] [Flat g] [RelativeDimension g s]
    (hf : f ≫ pY = pX) (hg : g ≫ pZ = pY) (k : ℤ)
    (α : Function.locallyFinsupp (Points Z) ℤ) :
    flatPullback pY pX δ f r hf (k + (s : ℤ))
        (flatPullback pZ pY δ g s hg k α) =
      flatPullback pZ pX δ (f ≫ g) (r + s) (comp_structureMorphism_eq hf hg)
        k α :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
