module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Cover
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Topology
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.ValuativeCriterion
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Plurigenus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Exercise 111.57.2 (Theorems) (1): the plurigenera of smooth proper varieties over a field
are invariant under birational equivalence. -/
@[stacks 0AAN] #check
  (@AlgebraicGeometry.SchemeOverField.plurigenus_eq_of_birational :
    ∀ {k : Type u} [Field k] (d : ℕ) (X Y : SchemeOverField k)
      [Variety X] [Variety Y] [IsProper X.hom] [IsProper Y.hom]
      [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d Y.hom]
      (h : Scheme.BirationalOver X.hom Y.hom) (n : ℕ),
        SchemeOverField.plurigenus X d n = SchemeOverField.plurigenus Y d n)

/- Exercise 111.57.2 (Theorems) (2): being an affine morphism is a local property on the target:
`f` is affine iff some affine open cover of the target has affine pullbacks. -/
@[stacks 0AAN] #check
  (@AlgebraicGeometry.isAffineHom_iff_exists_affineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      IsAffineHom f ↔
        ∃ 𝒰 : S.AffineOpenCover.{u},
          ∀ i : 𝒰.I₀, IsAffine ((𝒰.openCover.pullback₁ f).X i))

#check
  (inferInstance : IsZariskiLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u}))

/- Exercise 111.57.2 (Theorems) (3): the inclusion of the scheme-theoretic fibre is a topological
embedding with image the set-theoretic fibre `f ⁻¹' {y}`. -/
@[stacks 0AAN] #check
  (@AlgebraicGeometry.Scheme.Hom.fiberTopology :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y),
      Topology.IsEmbedding (f.fiberι y) ∧ Set.range (f.fiberι y) = f ⁻¹' {y})

#check
  (AlgebraicGeometry.Scheme.Hom.fiberHomeo :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y), f.fiber y ≃ₜ f ⁻¹' {y})

#check
  (AlgebraicGeometry.Scheme.Hom.range_fiberι :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y), Set.range (f.fiberι y) = f ⁻¹' {y})

/- Exercise 111.57.2 (Theorems) (4): a morphism is proper iff it satisfies the valuative criterion
and is quasi-compact, quasi-separated, and locally of finite type. -/
@[stacks 0AAN] #check
  (@AlgebraicGeometry.isProper_iff_valuativeCriterion :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      IsProper f ↔ ValuativeCriterion f ∧ QuasiCompact f ∧ QuasiSeparated f ∧
        LocallyOfFiniteType f)
