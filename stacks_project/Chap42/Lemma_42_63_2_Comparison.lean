module

public import ReasLib.AlgebraicGeometry.BivariantClass.Dedekind

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Dedekind

/- The compatibility surface used by the next source-facing lemma. -/
#check (baseMap : {S : Scheme.{u}} → (X : Over S) → X ⟶ Over.mk (𝟙 S))

#check (productIsPullback :
  {S : Scheme.{u}} → (X : Over S) → {Y : Over S} →
    (g : Y ⟶ Over.mk (𝟙 S)) →
    IsPullback ((Limits.prod.fst : X ⨯ Y ⟶ X).left)
      ((Limits.prod.snd : X ⨯ Y ⟶ Y).left) (baseMap X).left g.left)

#check (AlgebraicGeometry.BivariantClass.pointwiseZero :
  {S : Scheme.{u}} → [UniversallyCatenary S] →
    (delta : S → ℤ) → [IsDimensionFunction delta] →
    {X Y : Over S} → [LocallyOfFiniteType X.hom] → [LocallyOfFiniteType Y.hom] →
    (f : X ⟶ Y) → (p : ℤ) → BivariantClass delta f p)

#check (AlgebraicGeometry.BivariantClass.pointwiseAdd :
  {S : Scheme.{u}} → [UniversallyCatenary S] →
    (delta : S → ℤ) → [IsDimensionFunction delta] →
    {X Y : Over S} → [LocallyOfFiniteType X.hom] → [LocallyOfFiniteType Y.hom] →
    (f : X ⟶ Y) → (p : ℤ) →
    BivariantClass delta f p → BivariantClass delta f p → BivariantClass delta f p)

end AlgebraicGeometry.BivariantClass.Dedekind
