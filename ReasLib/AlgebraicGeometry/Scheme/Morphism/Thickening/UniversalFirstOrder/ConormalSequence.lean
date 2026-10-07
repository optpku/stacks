module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.Differentials
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Differentials

/-!
# Conormal sequences for universal first-order thickenings

The conormal map associated to a universal first-order thickening is transported across the
canonical comparison of pullbacks. It forms a right-exact sequence with the comparison on
relative differentials.
-/

@[expose] public section

open CategoryTheory
open scoped RelativeDerivation
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder.Differentials

variable {X S : Scheme.{u}}

/-- The canonical comparison from the pullback of `Ω_{X/S}` to the pullback of
`Ω_{Z'/S}` along the closed immersion into a universal first-order thickening. -/
noncomputable def pullbackComparison (T : Thickening.Over X) (f : X ⟶ S) :
    (pullback T.left.hom).obj Ω[f.toShHom] ⟶
      (pullback T.hom.left).obj Ω[(T.right.hom ≫ f).toShHom] :=
  (pullbackCongr T.hom.w).inv.app Ω[f.toShHom] ≫
    (pullbackComp T.hom.left T.right.hom).inv.app Ω[f.toShHom] ≫
      (pullback T.hom.left).map
        (Scheme.Hom.Conormal.Differentials.comparison T.right.hom f)

/-- The canonical pullback comparison for a universal first-order thickening of a
formally unramified morphism is an isomorphism. -/
instance pullbackComparison_isIso (T : Thickening.Over X) (f : X ⟶ S)
    [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T] :
    IsIso (pullbackComparison T f) :=
  AlgebraicGeometry.Thickening.IsUniversalFirstOrder.pullbackDifferentialsComparison_isIso T f

/-- The canonical isomorphism identifying the two middle terms of the conormal
sequences associated to a universal first-order thickening. -/
noncomputable def pullbackComparisonIso (T : Thickening.Over X) (f : X ⟶ S)
    [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T] :
    (pullback T.left.hom).obj Ω[f.toShHom] ≅
      (pullback T.hom.left).obj Ω[(T.right.hom ≫ f).toShHom] :=
  asIso (pullbackComparison T f)

/-- The conormal map for the closed immersion into a universal first-order neighbourhood,
transported to the pullback of `Ω_{X/S}`. -/
noncomputable def conormalMap (T : Thickening.Over X) (f : X ⟶ S)
    [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T] :
    IsUniversalFirstOrder.conormalSheaf T ⟶
      (pullback T.left.hom).obj Ω[f.toShHom] :=
  Scheme.Hom.Conormal.Differentials.map T.hom.left (T.right.hom ≫ f) ≫
    (pullbackComparisonIso T f).inv

/-- Composing the transported conormal map with the canonical pullback comparison
recovers the conormal map induced by the universal differential. -/
theorem conormalMap_comp_pullbackComparison (T : Thickening.Over X) (f : X ⟶ S)
    [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T] :
    conormalMap T f ≫ pullbackComparison T f =
      Scheme.Hom.Conormal.Differentials.map T.hom.left (T.right.hom ≫ f) := sorry

/-- The transported conormal map followed by the relative-differentials comparison
is zero. -/
theorem conormalMap_comp_comparison (T : Thickening.Over X) (f : X ⟶ S)
    [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T] :
    conormalMap T f ≫
      Scheme.Hom.Conormal.Differentials.comparison T.left.hom f = 0 := sorry

/-- The canonical conormal short complex associated to a universal first-order
thickening of a formally unramified morphism. -/
noncomputable def complex (T : Thickening.Over X) (f : X ⟶ S)
    [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T] :
    ShortComplex T.left.left.Modules :=
  ShortComplex.mk (conormalMap T f)
    (Scheme.Hom.Conormal.Differentials.comparison T.left.hom f)
    (conormalMap_comp_comparison T f)

/-- The canonical conormal short complex transported through a universal first-order
thickening is exact. -/
theorem exact (T : Thickening.Over X) (f : X ⟶ S)
    [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T] :
    (complex T f).Exact := sorry

/-- The canonical conormal complex transported through a universal first-order thickening is
exact, and its relative-differentials comparison is an epimorphism. -/
theorem exact_and_epi (T : Thickening.Over X) (f : X ⟶ S)
    [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T] :
    (complex T f).Exact ∧
      Epi (Scheme.Hom.Conormal.Differentials.comparison T.left.hom f) :=
  ⟨exact T f,
    Scheme.Hom.Conormal.Differentials.comparison_epi_of_formallyUnramified T.left.hom f⟩

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder.Differentials
