module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Graph
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The graph map `(f, 𝟙 Y) : Y ⟶ X ×ₖ Y` of a morphism of schemes over a field. -/
noncomputable def graph {k : Type u} [Field k]
    {X Y : SchemeOverField k} (f : Y ⟶ X) :
    Y.left ⟶ pullback X.hom Y.hom :=
  pullback.lift f.left (𝟙 Y.left) (CategoryTheory.Over.w f)

/-- The first projection of the graph map is the original morphism. -/
theorem graph_fst {k : Type u} [Field k]
    {X Y : SchemeOverField k} (f : Y ⟶ X) :
    graph f ≫ pullback.fst X.hom Y.hom = f.left := sorry

/-- The second projection of the graph map is the identity of its source. -/
theorem graph_snd {k : Type u} [Field k]
    {X Y : SchemeOverField k} (f : Y ⟶ X) :
    graph f ≫ pullback.snd X.hom Y.hom = 𝟙 Y.left := sorry

/-- The graph into `X ×ₖ Y` is a closed immersion when `X` is separated over the field. -/
instance graph_isClosedImmersion {k : Type u} [Field k]
    {X Y : SchemeOverField k} [IsSeparated X.hom] (f : Y ⟶ X) :
    IsClosedImmersion (graph f) := sorry

end AlgebraicGeometry.SchemeOverField
