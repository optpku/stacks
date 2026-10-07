module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.FittingIdeal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry RelativeDerivation

universe u

namespace AlgebraicGeometry

/-- A scheme morphism is at worst nodal when it is syntomic of relative dimension one and
the singular subscheme cut out by the first Fitting ideal of its relative differentials is
unramified over the base. -/
class AtWorstNodal {X S : Scheme.{u}} (f : X ⟶ S) : Prop
    extends SyntomicOfRelativeDimension f 1 where
  /-- The first-Fitting singular subscheme is unramified over the base. -/
  singularUnramified :
    Unramified ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) 1).subschemeι ≫ f)

/-- At-worst-nodality is equivalent to being syntomic of relative dimension one with
unramified first-Fitting singular subscheme. -/
theorem atWorstNodal_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    AtWorstNodal f ↔
      SyntomicOfRelativeDimension f 1 ∧
        Unramified ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) 1).subschemeι ≫ f) := by
  constructor
  · intro h
    exact ⟨h.toSyntomicOfRelativeDimension, h.singularUnramified⟩
  · rintro ⟨h, hu⟩
    exact { toSyntomicOfRelativeDimension := h, singularUnramified := hu }

/-- A scheme morphism is flat and locally of finite presentation, with every nonempty fibre
equidimensional of dimension one and all fibres at worst nodal, if and only if it is syntomic
of relative dimension one and its first-Fitting singular subscheme is unramified over the
base. -/
theorem fibersAtWorstNodal_iff_syntomicAndSingularUnramified
    {X S : Scheme.{u}} (f : X ⟶ S) :
    ((Flat f ∧ LocallyOfFinitePresentation f) ∧
        Scheme.Hom.RelativeDimension f 1 ∧
          ∀ s : S,
            SchemeOverField.atWorstNodal (Over.mk (f.fiberOverSpecResidueField s).hom)) ↔
      SyntomicOfRelativeDimension f 1 ∧
        Unramified ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) 1).subschemeι ≫ f) := sorry

namespace AtWorstNodal

/-- An étale precomposition of an at-worst-nodal morphism is at worst nodal. -/
instance etaleComp {Y X S : Scheme.{u}} (e : Y ⟶ X) (f : X ⟶ S)
    [Etale e] [AtWorstNodal f] : AtWorstNodal (e ≫ f) := sorry

/-- An étale postcomposition of an at-worst-nodal morphism is at worst nodal. -/
instance compEtale {X S' S : Scheme.{u}} (f : X ⟶ S') (e : S' ⟶ S)
    [AtWorstNodal f] [Etale e] : AtWorstNodal (f ≫ e) := sorry

/-- At-worst-nodality is preserved by arbitrary base change. -/
instance baseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [AtWorstNodal f] : AtWorstNodal (pullback.snd f g) := sorry

/-- An at-worst-nodal morphism has relative dimension at most one. -/
instance relativeDimensionLE {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] :
    Scheme.Hom.RelativeDimensionLE f 1 := sorry

/-- An at-worst-nodal morphism has geometrically reduced fibres. -/
instance geometricallyReduced {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] :
    GeometricallyReduced f := sorry

end AtWorstNodal

namespace SmoothOfRelativeDimension

/-- A smooth morphism of relative dimension one is at worst nodal. -/
instance atWorstNodal {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] :
    AtWorstNodal f := sorry

end SmoothOfRelativeDimension
end AlgebraicGeometry
