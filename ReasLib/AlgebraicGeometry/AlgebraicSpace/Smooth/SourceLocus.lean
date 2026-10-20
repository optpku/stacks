module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-! # The smooth source locus of a morphism of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Smooth

/-- The set of points at which a morphism of algebraic spaces is smooth is open. -/
theorem isOpen_smoothAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsOpen (setOf (SmoothAt f)) :=
  sorry

/-- The open subspace of points at which a morphism of algebraic spaces is smooth. -/
def sourceLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    OpenSubspace X :=
  OpenSubspace.fromOpens ⟨setOf (SmoothAt f), isOpen_smoothAt f⟩

/-- A point lies in the smooth source locus exactly when the morphism is smooth there. -/
theorem mem_sourceLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    x ∈ Set.range (Points.map (sourceLocus f).ι) ↔ SmoothAt f x := by
  exact Set.ext_iff.mp
    (OpenSubspace.fromOpens_pointsSet (X := X)
      ⟨setOf (SmoothAt f), isOpen_smoothAt f⟩) x

/-- The smooth source locus is smooth over the target and contains every open
subspace on which the morphism is smooth. -/
theorem sourceLocus_isLargest {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    Smooth ((sourceLocus f).ι ≫ f) ∧
      ∀ {U : AlgebraicSpace S} (i : U ⟶ X) [IsOpenImmersion i],
        Smooth (i ≫ f) →
          Set.range (Points.map i) ⊆ Set.range (Points.map (sourceLocus f).ι) :=
  sorry

/-- Every smooth open restriction has its point image contained in the smooth source locus. -/
theorem sourceLocus_maximal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U : AlgebraicSpace S} (i : U ⟶ X) [IsOpenImmersion i]
    (hf : Smooth (i ≫ f)) :
    Set.range (Points.map i) ⊆ Set.range (Points.map (sourceLocus f).ι) :=
  (sourceLocus_isLargest f).2 i hf

/-- In a cartesian square of algebraic spaces, pointwise smoothness is preserved
and reflected when the base morphism is flat and locally of finite presentation. -/
theorem smoothAt_iff_of_isPullback_of_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) [Flat g] [LocallyOfFinitePresentation g]
    (x' : Points X') :
    SmoothAt f' x' ↔ SmoothAt f (Points.map g' x') :=
  sorry

/-- In a cartesian square of algebraic spaces over a flat base morphism,
pointwise smoothness is preserved and reflected when the original morphism is
locally of finite presentation. -/
theorem smoothAt_iff_of_isPullback_of_flat_base
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [Flat g]
    (x' : Points X') :
    SmoothAt f' x' ↔ SmoothAt f (Points.map g' x') :=
  sorry

/-- The smooth source locus pulls back along flat morphisms locally of finite presentation. -/
theorem sourceLocus_eq_preimage_of_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) [Flat g] [LocallyOfFinitePresentation g] :
    Set.range (Points.map (sourceLocus f').ι) =
      (Points.map g') ⁻¹' Set.range (Points.map (sourceLocus f).ι) := by
  apply Set.ext
  intro x'
  exact (mem_sourceLocus f' x').trans
    ((smoothAt_iff_of_isPullback_of_flat_locallyOfFinitePresentation
      g' f' f g hcart x').trans (mem_sourceLocus f (Points.map g' x')).symm)

/-- The smooth source locus of a morphism locally of finite presentation pulls
back along flat morphisms. -/
theorem sourceLocus_eq_preimage_of_flat_base
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [Flat g] :
    Set.range (Points.map (sourceLocus f').ι) =
      (Points.map g') ⁻¹' Set.range (Points.map (sourceLocus f).ι) := by
  apply Set.ext
  intro x'
  exact (mem_sourceLocus f' x').trans
    ((smoothAt_iff_of_isPullback_of_flat_base g' f' f g hcart x').trans
      (mem_sourceLocus f (Points.map g' x')).symm)

end AlgebraicGeometry.AlgebraicSpace.Smooth
