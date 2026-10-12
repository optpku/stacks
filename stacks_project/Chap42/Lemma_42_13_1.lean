/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFormula.Flat

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace DimensionFormula

/- Lemma 42.13.1 (1): a flat morphism of relative dimension `r` shifts the
`δ`-dimension of every closed subset with nonempty inverse image by `r`. -/
@[stacks 02R8] #check
  (AlgebraicGeometry.Scheme.Hom.DimensionFormula.closedPreimageDeltaDimension :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) (r : ℕ) [Flat f.left] [RelativeDimension f.left r]
      (Z : Closeds Y.left) (hZ : Nonempty (Z.preimage f.left.continuous)),
      X.hom.closedSubschemeDeltaDimension δ
          (IdealSheafData.vanishingIdeal (Z.preimage f.left.continuous)) =
        Y.hom.closedSubschemeDeltaDimension δ (IdealSheafData.vanishingIdeal Z) +
          (r : EInt))

/- Lemma 42.13.1 (2): every irreducible component of the inverse image of an
irreducible closed subset dominates that subset. -/
@[stacks 02R8] #check
  (AlgebraicGeometry.Scheme.Hom.DimensionFormula.componentOfPreimageMapsTo :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) (r : ℕ) [Flat f.left] [RelativeDimension f.left r]
      (Z : IrreducibleCloseds Y.left) (Z' : IrreducibleCloseds X.left)
      (hZ' : Maximal (fun W : IrreducibleCloseds X.left ↦
        (W : Set X.left) ⊆ f.left ⁻¹' (Z : Set Y.left)) Z'),
      IrreducibleCloseds.map f.left f.left.continuous Z' = Z)

/- Lemma 42.13.1 (3): every irreducible component of the inverse image of an
irreducible closed subset has `δ`-dimension shifted by the relative dimension `r`. -/
@[stacks 02R8] #check
  (AlgebraicGeometry.Scheme.Hom.DimensionFormula.componentOfPreimageDeltaDimension :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) (r : ℕ) [Flat f.left] [RelativeDimension f.left r]
      (Z : IrreducibleCloseds Y.left) (Z' : IrreducibleCloseds X.left)
      (hZ' : Maximal (fun W : IrreducibleCloseds X.left ↦
        (W : Set X.left) ⊆ f.left ⁻¹' (Z : Set Y.left)) Z'),
      X.hom.deltaDimension δ Z' = Y.hom.deltaDimension δ Z + (r : ℤ))

end DimensionFormula
end Hom
end Scheme
end AlgebraicGeometry
