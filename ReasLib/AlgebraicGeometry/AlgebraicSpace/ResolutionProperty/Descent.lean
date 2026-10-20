module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-!
# Affine étale descent data for the resolution property

A quasi-compact absolutely quasi-separated algebraic space may be equipped with a chosen
affine étale surjection, a finite factorization through an open immersion, and a
finite-type quasi-coherent ideal cutting out the closed complement of that open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Chosen affine étale cover, open-immersion/finite factorization, and finite-type
quasi-coherent vanishing ideal on a quasi-compact absolutely quasi-separated algebraic space. -/
structure ResolutionDescent {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] where
  /-- An affine scheme `V` over `S`, viewed in `Over S`. -/
  V : Over S
  /-- The scheme `V.left` is affine. -/
  isAffine_V : IsAffine V.left
  /-- The chosen morphism `φ : ofOver V ⟶ X`. -/
  φ : ofOver V ⟶ X
  /-- The morphism `φ` is étale. -/
  etale_φ : Etale φ
  /-- The morphism `φ` is surjective. -/
  surjective_φ : Surjective φ
  /-- The intermediate algebraic space in the finite factorization of `φ`. -/
  Y : AlgebraicSpace S
  /-- The open immersion `j : ofOver V ⟶ Y`. -/
  j : ofOver V ⟶ Y
  /-- The finite morphism `π : Y ⟶ X`. -/
  π : Y ⟶ X
  /-- The morphism `j` is an open immersion. -/
  isOpenImmersion_j : IsOpenImmersion j
  /-- The morphism `π` is finite. -/
  isFinite_π : IsFinite π
  /-- The triangle commutes: `j ≫ π = φ`. -/
  comm : j ≫ π = φ
  /-- A quasi-coherent ideal sheaf `I ⊂ 𝒪_Y`. -/
  I : IdealSubobject Y
  /-- The ideal sheaf `I` is quasi-coherent. -/
  isQuasiCoherent_I : IsQuasiCoherent I
  /-- The ideal sheaf `I` is of finite type as an `𝒪_Y`-module. -/
  isFiniteType_I : (I : Y.Modules).IsFiniteType
  /-- The vanishing locus of `I` is the complement of the image of `j`. -/
  vanishing :
    (@ClosedSubspace.ofQuasiCoherentIdeal _ _ I isQuasiCoherent_I).pointsSet =
      (Set.range (Points.map j))ᶜ

namespace ResolutionDescent

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]

/-- Package an affine étale cover, an open-immersion/finite factorization, and a
finite-type quasi-coherent vanishing ideal as descent data on `X`. -/
def of {V : Over S} [IsAffine V.left] (φ : ofOver V ⟶ X) [Etale φ] [Surjective φ]
    (Y : AlgebraicSpace S) (j : ofOver V ⟶ Y) (π : Y ⟶ X)
    [IsOpenImmersion j] [IsFinite π] (comm : j ≫ π = φ)
    (I : IdealSubobject Y) [IsQuasiCoherent I] [(I : Y.Modules).IsFiniteType]
    (vanishing :
      (ClosedSubspace.ofQuasiCoherentIdeal I).pointsSet = (Set.range (Points.map j))ᶜ) :
    ResolutionDescent X where
  V := V
  isAffine_V := inferInstance
  φ := φ
  etale_φ := inferInstance
  surjective_φ := inferInstance
  Y := Y
  j := j
  π := π
  isOpenImmersion_j := inferInstance
  isFinite_π := inferInstance
  comm := comm
  I := I
  isQuasiCoherent_I := inferInstance
  isFiniteType_I := inferInstance
  vanishing := vanishing

/-- The open subspace of `Y` determined by the open immersion `j`. -/
def openImmersionSubspace (sit : ResolutionDescent X) : OpenSubspace sit.Y where
  X := ofOver sit.V
  ι := sit.j
  isOpenImmersion := sit.isOpenImmersion_j

/-- The closed subspace of `Y` cut out by the chosen ideal `I`. -/
def vanishingClosedSubspace (sit : ResolutionDescent X) : ClosedSubspace sit.Y :=
  @ClosedSubspace.ofQuasiCoherentIdeal _ _ sit.I sit.isQuasiCoherent_I

/-- Descent data consists of an affine étale surjection `φ`, an open immersion `j`
and finite morphism `π` with `j ≫ π = φ`, and a finite-type quasi-coherent ideal
whose vanishing locus is the complement of the image of `j`. -/
theorem spec (sit : ResolutionDescent X) :
    IsAffine sit.V.left ∧ Etale sit.φ ∧ Surjective sit.φ ∧
      IsOpenImmersion sit.j ∧ IsFinite sit.π ∧ sit.j ≫ sit.π = sit.φ ∧
      IsQuasiCoherent sit.I ∧ (sit.I : sit.Y.Modules).IsFiniteType ∧
      sit.vanishingClosedSubspace.pointsSet = (Set.range (Points.map sit.j))ᶜ :=
  sorry

/-- The vanishing locus of `I` is the complement of the open image of `j`. -/
theorem vanishing_eq (sit : ResolutionDescent X) :
    sit.vanishingClosedSubspace.pointsSet = sit.openImmersionSubspace.pointsSetᶜ :=
  sorry

/-- The chosen cover `φ` is étale as a morphism of functors of points. -/
theorem etale_presheaf (sit : ResolutionDescent X) :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf sit.φ :=
  sorry

/-- The chosen cover `φ` is locally surjective for the étale topology over `S`. -/
theorem locallySurjective_φ (sit : ResolutionDescent X) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) sit.φ :=
  sorry

/-- A quasi-compact absolutely quasi-separated algebraic space admits affine étale covers,
finite factorizations, and finite-type vanishing ideals of this shape. -/
theorem nonempty (X : AlgebraicSpace S) [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] : Nonempty (ResolutionDescent X) :=
  sorry

end ResolutionDescent

end AlgebraicGeometry.AlgebraicSpace
