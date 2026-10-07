module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.29.3 (1): relative-dimension upper bounds add under composition. -/
@[stacks 02NL] #check
  (AlgebraicGeometry.Scheme.Hom.relativeDimensionLE_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} {d e : ℕ}
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE f d]
      [AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE g e],
      AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE (f ≫ g) (d + e))

/- Lemma 29.29.3 (2): fixed relative dimensions add under composition when the
first morphism is flat. -/
@[stacks 02NL] #check
  (AlgebraicGeometry.Scheme.Hom.relativeDimension_comp_of_flat :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} {d e : ℕ}
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.Scheme.Hom.RelativeDimension f d]
      [AlgebraicGeometry.Scheme.Hom.RelativeDimension g e]
      [AlgebraicGeometry.Flat f],
      AlgebraicGeometry.Scheme.Hom.RelativeDimension (f ≫ g) (d + e))
