module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback.Composition
import StacksCheckRecall

/-!
# Composition of flat pullbacks of cycles

For good algebraic spaces over a dimension-function base, flat morphisms have
additive relative dimensions and their flat pullbacks compose on graded cycles.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/- Lemma 82.10.4: Flat pullbacks along composable flat morphisms agree with
pullback along the composite on degree-`k` cycles. -/
@[stacks 0EPA]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_comp :
  ∀ {S : Scheme.{u}} {B X Y Z : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pZ : Z ⟶ B) [QuasiSeparated pZ] [LocallyOfFiniteType pZ]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [LocallyOfFiniteType f] [Flat f] [RelativeDimension f r]
    (g : Y ⟶ Z) (s : ℕ) [LocallyOfFiniteType g] [Flat g] [RelativeDimension g s]
    (hf : f ≫ pY = pX) (hg : g ≫ pZ = pY) (k : ℤ)
    (α : (cycleGroup pZ) δ k),
    flatPullback pY pX δ f r hf (k + (s : ℤ))
        (flatPullback pZ pY δ g s hg k α) =
      flatPullback pZ pX δ (f ≫ g) (r + s) (by rw [Category.assoc, hg, hf])
        k α)

#check (AlgebraicGeometry.AlgebraicSpace.instRelativeDimension_comp_of_flat :
  ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : ℕ)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [Flat f] [RelativeDimension f r] [RelativeDimension g s],
    RelativeDimension (f ≫ g) (r + s))

end AlgebraicGeometry.AlgebraicSpace.Hom
