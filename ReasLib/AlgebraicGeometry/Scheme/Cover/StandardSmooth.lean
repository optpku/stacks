module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Smooth
public import ReasLib.CategoryTheory.Sites.Family

/-!
# Standard smooth covering families

The finite affine chart presentation is stronger than an arbitrary smooth
covering family and is kept as explicit data for refinements and local
computations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u

namespace AlgebraicGeometry

/-- A finite affine covering family of an affine scheme whose global-section maps are standard
smooth. -/
structure StandardSmoothCovering (T : Scheme.{u}) [IsAffine T] where
  /-- The number of affine charts. -/
  n : ℕ
  /-- The affine source schemes of the charts. -/
  U : Fin n → Scheme.{u}
  /-- The chart maps to the affine target. -/
  map : ∀ j, U j ⟶ T
  /-- Each source chart is affine. -/
  isAffine : ∀ j, IsAffine (U j)
  /-- Each global-sections map is standard smooth. -/
  isStandardSmooth :
    ∀ j, RingHom.IsStandardSmooth (CommRingCat.Hom.hom (Scheme.Hom.appTop (map j)))
  /-- The images of the charts cover every point of the target. -/
  cover : ∀ t : T, ∃ j, t ∈ Set.range (map j)

/-- Construct a standard smooth covering from a finite affine family whose
global-sections maps are standard smooth and whose images cover the target. -/
def StandardSmoothCovering.ofAffineFamily
    {T : Scheme.{u}} [IsAffine T] (family : AffineFamilyOver T)
    (isStandardSmooth :
      ∀ j, RingHom.IsStandardSmooth
        (CommRingCat.Hom.hom (Scheme.Hom.appTop (family.map j))))
    (cover : ∀ t : T, ∃ j, t ∈ Set.range (family.map j)) :
    StandardSmoothCovering T where
  n := family.n
  U := family.U
  map := family.map
  isAffine := family.isAffine
  isStandardSmooth := isStandardSmooth
  cover := cover

/-- The defining affine, standard-smooth, and covering data of a standard smooth covering. -/
theorem StandardSmoothCovering.source_spec
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) :
    (∀ j, IsAffine (𝒰.U j)) ∧
      (∀ j, RingHom.IsStandardSmooth (CommRingCat.Hom.hom (Scheme.Hom.appTop (𝒰.map j)))) ∧
        (∀ t : T, ∃ j, t ∈ Set.range (𝒰.map j)) := sorry

/-- The finite affine family underlying a standard smooth covering. -/
def StandardSmoothCovering.toAffineFamily
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) :
    AffineFamilyOver T where
  n := 𝒰.n
  U := 𝒰.U
  map := 𝒰.map
  isAffine := 𝒰.isAffine

/-- The `j`-th chart map of the affine family underlying a standard smooth
covering is its original chart map. -/
@[simp]
theorem StandardSmoothCovering.toAffineFamily_map
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) (j : Fin 𝒰.n) :
    𝒰.toAffineFamily.map j = 𝒰.map j := sorry

/-- The global-sections map of a standard smooth chart is standard smooth. -/
theorem StandardSmoothCovering.appTop_isStandardSmooth
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) (j : Fin 𝒰.n) :
    RingHom.IsStandardSmooth (CommRingCat.Hom.hom (Scheme.Hom.appTop (𝒰.map j))) := sorry

/-- The fixed-target family associated to a standard smooth covering. -/
abbrev StandardSmoothCovering.toOverFamily
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) :
    SemiRepresentableFamily.Over T :=
  ofArrows 𝒰.U 𝒰.map

/-- Every chart map in a standard smooth covering is smooth. -/
theorem StandardSmoothCovering.smooth_map
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) (j : Fin 𝒰.n) :
    Smooth (𝒰.map j) := sorry

/-- The union of the chart images of a standard smooth covering is all of the target. -/
theorem StandardSmoothCovering.iUnion_range_eq_univ
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) :
    (⋃ j, Set.range (𝒰.map j)) = Set.univ := sorry

/-- A standard smooth covering generates a covering presieve in the smooth precoverage. -/
theorem StandardSmoothCovering.mem_smooth_precoverage
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) :
    Presieve.ofArrows 𝒰.U 𝒰.map ∈ (Scheme.precoverage @Smooth).coverings T := sorry

/-- A standard smooth covering induces a canonical smooth covering family. -/
theorem StandardSmoothCovering.smoothCovering
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSmoothCovering T) :
    Scheme.SmoothCovering (𝒰.toOverFamily.obj) := sorry

end AlgebraicGeometry
