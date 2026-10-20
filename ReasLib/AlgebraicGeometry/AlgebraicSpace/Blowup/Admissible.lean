module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-!
# Admissible blowups of algebraic spaces

Blowups are characterized by the effective-Cartier universal property. An
admissible center is finitely presented and disjoint from a specified open subspace.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism is the blowup in a closed subspace when its inverse image is an
effective Cartier divisor and it is terminal among morphisms with this property. -/
def IsBlowup {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (f : X' ⟶ X) (Z : ClosedSubspace X) : Prop :=
  IsEffectiveCartierDivisor (Z.inverseImageSubspace f).ι ∧
    ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X),
      IsEffectiveCartierDivisor (Z.inverseImageSubspace g).ι →
        ExistsUnique fun h : Y ⟶ X' ↦ h ≫ f = g

/-- The inverse image of the center of a blowup is an effective Cartier divisor. -/
theorem IsBlowup.inverseImage_isEffectiveCartier
    {S : Scheme.{u}} {X X' : AlgebraicSpace S} {f : X' ⟶ X} {Z : ClosedSubspace X}
    (h : IsBlowup f Z) : IsEffectiveCartierDivisor (Z.inverseImageSubspace f).ι :=
  h.1

/-- Every morphism making the center effective Cartier factors uniquely through its blowup. -/
theorem IsBlowup.existsUnique_lift {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {f : X' ⟶ X} {Z : ClosedSubspace X} (h : IsBlowup f Z) {Y : AlgebraicSpace S}
    (g : Y ⟶ X) (hg : IsEffectiveCartierDivisor (Z.inverseImageSubspace g).ι) :
    ExistsUnique fun h' : Y ⟶ X' ↦ h' ≫ f = g :=
  h.2 g hg

/-- Being a blowup is equivalent to the effective-Cartier condition and its universal property. -/
theorem isBlowup_iff {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (f : X' ⟶ X) (Z : ClosedSubspace X) :
    IsBlowup f Z ↔
      IsEffectiveCartierDivisor (Z.inverseImageSubspace f).ι ∧
        ∀ {Y : AlgebraicSpace S} (g : Y ⟶ X),
          IsEffectiveCartierDivisor (Z.inverseImageSubspace g).ι →
            ExistsUnique fun h : Y ⟶ X' ↦ h ≫ f = g :=
  Iff.rfl

/-- The identity is the blowup in an effective Cartier divisor. -/
theorem isBlowup_id_of_isEffectiveCartierDivisor
    {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    [IsEffectiveCartierDivisor Z.ι] : IsBlowup (𝟙 X) Z :=
  sorry

/-- An admissible blowup center is a finitely presented closed subspace disjoint
from the specified open subspace, together with the blowup property. -/
def IsAdmissibleBlowupCenter {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (f : X' ⟶ X) (Z : ClosedSubspace X) : Prop :=
  IsBlowup f Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet

/-- An admissible blowup is a blowup in its specified center. -/
theorem IsAdmissibleBlowupCenter.isBlowup {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} {U : OpenSubspace X} {f : X' ⟶ X} {Z : ClosedSubspace X}
    (h : IsAdmissibleBlowupCenter U f Z) : IsBlowup f Z :=
  h.1

/-- The inclusion of an admissible center is of finite presentation. -/
theorem IsAdmissibleBlowupCenter.finitePresentation {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} {U : OpenSubspace X} {f : X' ⟶ X} {Z : ClosedSubspace X}
    (h : IsAdmissibleBlowupCenter U f Z) : FinitePresentation Z.ι :=
  h.2.1

/-- Admissibility is equivalent to the blowup property, finite presentation of the
center, and disjointness from the specified open subspace. -/
theorem isAdmissibleBlowupCenter_iff {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (f : X' ⟶ X) (Z : ClosedSubspace X) :
    IsAdmissibleBlowupCenter U f Z ↔
      IsBlowup f Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet :=
  Iff.rfl

/-- The identity is an admissible blowup with the empty center cut out by the unit ideal. -/
theorem isAdmissibleBlowupCenter_id {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : OpenSubspace X) :
    IsAdmissibleBlowupCenter U (𝟙 X)
      (ClosedSubspace.ofQuasiCoherentIdeal (⊤ : IdealSubobject X)) :=
  sorry

/-- An admissible blowup is an isomorphism over the specified open subspace. -/
theorem isIso_pullbackFst_of_isAdmissibleBlowupCenter
    {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (b : X' ⟶ X) (center : ClosedSubspace X)
    (h : IsAdmissibleBlowupCenter U b center) :
    IsIso (pullback.fst U.ι b) :=
  sorry

/-- A morphism is admissible over an open subspace when it is a blowup in a
finitely presented closed center disjoint from that open subspace. -/
def IsAdmissibleBlowup {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (f : X' ⟶ X) : Prop :=
  ∃ Z : ClosedSubspace X, IsAdmissibleBlowupCenter U f Z

/-- An admissible center exhibits a morphism as an admissible blowup. -/
theorem IsAdmissibleBlowup.mk {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {U : OpenSubspace X} {f : X' ⟶ X} (Z : ClosedSubspace X)
    (h : IsAdmissibleBlowupCenter U f Z) : IsAdmissibleBlowup U f :=
  ⟨Z, h⟩

/-- Every admissible blowup has an admissible center. -/
theorem IsAdmissibleBlowup.exists_center {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    {U : OpenSubspace X} {f : X' ⟶ X} (hf : IsAdmissibleBlowup U f) :
    ∃ Z : ClosedSubspace X, IsAdmissibleBlowupCenter U f Z :=
  hf

/-- An admissible blowup has a finitely presented center disjoint from the
specified open subspace for which the morphism is a blowup. -/
theorem IsAdmissibleBlowup.exists_center_spec {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} {U : OpenSubspace X} {f : X' ⟶ X}
    (hf : IsAdmissibleBlowup U f) :
    ∃ Z : ClosedSubspace X,
      IsBlowup f Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet :=
  hf

/-- Admissibility is equivalent to being a blowup in a finitely presented center
disjoint from the specified open subspace. -/
theorem isAdmissibleBlowup_iff {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (U : OpenSubspace X) (f : X' ⟶ X) :
    IsAdmissibleBlowup U f ↔
      ∃ Z : ClosedSubspace X,
        IsBlowup f Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet :=
  Iff.rfl

/-- The identity is admissible over every open subspace. -/
theorem IsAdmissibleBlowup.id {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : OpenSubspace X) : IsAdmissibleBlowup U (𝟙 X) :=
  ⟨ClosedSubspace.ofQuasiCoherentIdeal (⊤ : IdealSubobject X),
    isAdmissibleBlowupCenter_id U⟩

end AlgebraicGeometry.AlgebraicSpace
