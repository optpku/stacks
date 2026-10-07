module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import stacks_project.Chap63.Lemma_63_2_1_SectionsSupportedIn

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
variable {U U' : X.Etale} (φ : U' ⟶ U) {Z' : Scheme.{u}} (ι : Z' ⟶ U'.left)
variable [IsClosedImmersion ι] [IsClosedImmersion (ι ≫ φ.left)]

/-- The residual closed set `T = φ⁻¹(Z) \ Z'` on `U'`, where `Z` is the image of
`ι ≫ φ.left`. -/
def residualClosedSet : Set U'.left :=
  (φ.left ⁻¹' Set.range (ι ≫ φ.left)) \ Set.range ι

/-- The complement of `residualClosedSet` is open. -/
theorem isOpen_compl_residualClosedSet :
    IsOpen (residualClosedSet φ ι)ᶜ := sorry

/-- The residual open `U' \ T` complementary to `residualClosedSet`. -/
def residualOpen : U'.left.Opens :=
  ⟨(residualClosedSet φ ι)ᶜ, isOpen_compl_residualClosedSet φ ι⟩

/-- The underlying set of the residual open is the complement of `residualClosedSet`. -/
theorem residualOpen_carrier :
    (residualOpen φ ι : Set U'.left) = (residualClosedSet φ ι)ᶜ :=
  sorry

/-- The residual open `U' \ T` as an object of `X.Etale`. -/
abbrev residualEtale : X.Etale :=
  mk ((residualOpen φ ι).ι ≫ U'.hom)

/-- The residual open immersion composed with `φ` lies over `X`. -/
theorem residualHomOver_w :
    ((residualOpen φ ι).ι ≫ φ.left) ≫ U.hom = (residualEtale φ ι).hom :=
  sorry

/-- The open immersion of the residual open into `U'`, as a morphism of `X.Etale`. -/
abbrev residualHom : residualEtale φ ι ⟶ U' :=
  MorphismProperty.Over.homMk (residualOpen φ ι).ι

/-- The composite of the residual open immersion with `φ`, as a morphism of `X.Etale`. -/
abbrev residualHomOver : residualEtale φ ι ⟶ U :=
  MorphismProperty.Over.homMk ((residualOpen φ ι).ι ≫ φ.left) (residualHomOver_w φ ι)

/-- The closed image of `Z'` viewed on the residual open of `U'`. -/
def residualSupport : Set (residualEtale φ ι).left :=
  (residualOpen φ ι).ι ⁻¹' Set.range ι

/-- Restriction of sections supported in `Z'` from `U'` to the residual open. -/
def restrictSupportedInResidual :
    abelianSheafSectionsSupportedIn F U' (Set.range ι) →+
      abelianSheafSectionsSupportedIn F (residualEtale φ ι) (residualSupport φ ι) where
  toFun σ := ⟨F.1.map (residualHom φ ι).op σ.val, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- Restriction of sections supported in the image of `Z'` from `U` to the residual open. -/
def restrictSupportedInResidualOver :
    abelianSheafSectionsSupportedIn F U (Set.range (ι ≫ φ.left)) →+
      abelianSheafSectionsSupportedIn F (residualEtale φ ι) (residualSupport φ ι) where
  toFun σ := ⟨F.1.map (residualHomOver φ ι).op σ.val, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- Lemma 63.2.1: for a scheme `X`, an abelian sheaf `F` on `X_étale`, a morphism
`φ : U' ⟶ U` of `X_étale`, and a closed subscheme `ι : Z' ⟶ U'.left` whose
composite `ι ≫ φ.left` is a closed immersion with image `Z ⊂ U`, there is a
canonical bijection between sections of `F` on `U` supported in `Z` and sections
of `F` on `U'` supported in `Z'`. When `φ.left ⁻¹' Z = Z'` this bijection is
restriction along `φ`. -/
@[stacks 0F6F]
def abelianSheafSectionsSupportedInAddEquiv :
    abelianSheafSectionsSupportedIn F U (Set.range (ι ≫ φ.left)) ≃+
      abelianSheafSectionsSupportedIn F U' (Set.range ι) :=
  (AddEquiv.ofBijective (restrictSupportedInResidualOver F φ ι) sorry).trans
    (AddEquiv.ofBijective (restrictSupportedInResidual F φ ι) sorry).symm

/-- If `φ⁻¹(Z) = Z'`, the canonical comparison of supported sections is restriction along `φ`. -/
theorem abelianSheafSectionsSupportedInAddEquiv_apply_of_preimage_eq
    (h_preimage : φ.left ⁻¹' Set.range (ι ≫ φ.left) = Set.range ι)
    (σ : abelianSheafSectionsSupportedIn F U (Set.range (ι ≫ φ.left))) :
    (abelianSheafSectionsSupportedInAddEquiv F φ ι σ).val = F.1.map φ.op σ.val :=
  sorry


end AlgebraicGeometry.Scheme.Etale

end
