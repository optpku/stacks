module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
public import stacks_project.Chap88.Definition_88_21_1_Formal
public import stacks_project.Chap88.Definition_88_21_1_Spf

/-!
# Adic formal-spectrum squares

A solid adic `Spf` square over a morphism `f : X ⟶ Y` packages a complete
discrete valuation ring `R`, a structure morphism `Spec(R) ⟶ S`, and an adic
test map `Spf(R) ⟶ Y`. An extension fills the dotted arrow after an extension
of complete discrete valuation rings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A solid adic `Spf` square over `f : X ⟶ Y` is a complete discrete valuation
ring `R`, a structure morphism `Spec(R) ⟶ S`, and an adic morphism
`Spf(R) ⟶ Y`. -/
structure AdicSpfSquare {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) where
  /-- The complete discrete valuation ring of the solid diagram. -/
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [discreteValuationRing : IsDiscreteValuationRing R]
  [completeLocalRing : IsCompleteLocalRing R]
  /-- The structure morphism of `Spec(R)` over `S`. -/
  structureHom : Spec (.of R) ⟶ S
  /-- The bottom map `Spf(R) ⟶ Y` of the solid diagram. -/
  p : spf R structureHom ⟶ Y
  /-- The test map `p` is an adic morphism, equivalently representable by
  algebraic spaces. -/
  h_adic : AlgebraicSpace.representableByAlgebraicSpaces p

namespace AdicSpfSquare

attribute [instance] commRing domain discreteValuationRing completeLocalRing

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

/-- Construct a solid adic `Spf` square from a complete discrete valuation ring,
a structure morphism over `S`, and an adic test map. -/
def of (f : X ⟶ Y) (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] (structureHom : Spec (.of R) ⟶ S)
    (p : spf R structureHom ⟶ Y)
    (h_adic : AlgebraicSpace.representableByAlgebraicSpaces p) :
    AdicSpfSquare f where
  R := R
  structureHom := structureHom
  p := p
  h_adic := h_adic

/-- The test object `Spf(R)` of a solid adic square. -/
abbrev specSpf (sq : AdicSpfSquare f) : (Over S)ᵒᵖ ⥤ Type u :=
  spf sq.R sq.structureHom

/-- The structure morphism of `AdicSpfSquare.of` is the given morphism to `S`. -/
theorem of_structureHom (f : X ⟶ Y) (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] (structureHom : Spec (.of R) ⟶ S)
    (p : spf R structureHom ⟶ Y)
    (h_adic : AlgebraicSpace.representableByAlgebraicSpaces p) :
    (of f R structureHom p h_adic).structureHom = structureHom :=
  sorry

/-- A solid adic `Spf` square is given by a complete discrete valuation ring
together with an adic test map from its formal spectrum. -/
theorem spec (sq : AdicSpfSquare f) :
    IsDiscreteValuationRing sq.R ∧ IsCompleteLocalRing sq.R ∧
      AlgebraicSpace.representableByAlgebraicSpaces sq.p :=
  sorry

/-- An extension of a solid adic `Spf` square is an extension of complete
discrete valuation rings `R ⊂ R'` together with a morphism `Spf(R') ⟶ X`
making the displayed triangle commute. -/
structure Extension (sq : AdicSpfSquare f) where
  /-- The extended complete discrete valuation ring. -/
  R' : Type u
  [commRing : CommRing R']
  [domain : IsDomain R']
  [discreteValuationRing : IsDiscreteValuationRing R']
  [completeLocalRing : IsCompleteLocalRing R']
  [algebra : Algebra sq.R R']
  [isExtension : IsExtensionOfDiscreteValuationRings sq.R R']
  /-- A lift `Spf(R') ⟶ X` of the extended square. -/
  lift :
    spf R' (Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) ⟶ X
  /-- The displayed triangle commutes. -/
  fac : lift ≫ f = spfMap sq.R R' sq.structureHom ≫ sq.p

namespace Extension

attribute [instance] commRing domain discreteValuationRing completeLocalRing algebra isExtension

/-- Construct an extension of a solid adic `Spf` square from an extension of
complete discrete valuation rings and a commuting lift. -/
def of (sq : AdicSpfSquare f) (R' : Type u) [CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] [IsCompleteLocalRing R'] [Algebra sq.R R']
    [IsExtensionOfDiscreteValuationRings sq.R R']
    (lift : spf R' (Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) ⟶ X)
    (fac : lift ≫ f = spfMap sq.R R' sq.structureHom ≫ sq.p) :
    sq.Extension where
  R' := R'
  lift := lift
  fac := fac

/-- The vertical morphism `Spf(R') ⟶ Spf(R)` of an extended adic square. -/
abbrev verticalMap {sq : AdicSpfSquare f} (e : sq.Extension) :
    spf e.R' (Spec.map (CommRingCat.ofHom (algebraMap sq.R e.R')) ≫ sq.structureHom) ⟶
      specSpf sq :=
  spfMap sq.R e.R' sq.structureHom

/-- The two paths `Spf(R') ⟶ Y` of an extended adic square agree. -/
theorem spec {sq : AdicSpfSquare f} (e : sq.Extension) :
    e.lift ≫ f = e.verticalMap ≫ sq.p :=
  sorry

/-- The structure morphism of the extended `Spf(R')` is `Spec.map` of the algebra
map, composed with the original structure morphism. -/
theorem of_lift (sq : AdicSpfSquare f) (R' : Type u) [CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] [IsCompleteLocalRing R'] [Algebra sq.R R']
    [IsExtensionOfDiscreteValuationRings sq.R R']
    (lift : spf R' (Spec.map (CommRingCat.ofHom (algebraMap sq.R R')) ≫ sq.structureHom) ⟶ X)
    (fac : lift ≫ f = spfMap sq.R R' sq.structureHom ≫ sq.p) :
    (of sq R' lift fac).lift = lift :=
  sorry

end Extension

end AdicSpfSquare

end AlgebraicGeometry.FormalAlgebraicSpace
