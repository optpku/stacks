module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
public import ReasLib.AlgebraicGeometry.FormalSpectrum.CompleteDVR

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
  /-- The ring operations on the test ring. -/
  commRing : CommRing R
  /-- The test ring is a domain. -/
  domain : @IsDomain R commRing.toSemiring
  /-- The test ring is a discrete valuation ring. -/
  discreteValuationRing : @IsDiscreteValuationRing R commRing domain
  /-- The test ring is complete for its maximal-adic topology. -/
  completeLocalRing : @IsCompleteLocalRing R commRing
  /-- The structure morphism of `Spec(R)` over `S`. -/
  structureHom : Spec (@CommRingCat.of R commRing) ⟶ S
  /-- The bottom map `Spf(R) ⟶ Y` of the solid diagram. -/
  p : @spf R commRing domain discreteValuationRing completeLocalRing S structureHom ⟶ Y
  /-- The test map `p` is an adic morphism, equivalently representable by
  algebraic spaces. -/
  h_adic : AlgebraicSpace.representableByAlgebraicSpaces p

namespace AdicSpfSquare

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

/-- Construct a solid adic `Spf` square from a complete discrete valuation ring,
a structure morphism over `S`, and an adic test map. -/
@[reducible]
def of (f : X ⟶ Y) (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsCompleteLocalRing R] (structureHom : Spec (.of R) ⟶ S)
    (p : spf R structureHom ⟶ Y)
    (h_adic : AlgebraicSpace.representableByAlgebraicSpaces p) :
    AdicSpfSquare f where
  R := R
  commRing := inferInstance
  domain := inferInstance
  discreteValuationRing := inferInstance
  completeLocalRing := inferInstance
  structureHom := structureHom
  p := p
  h_adic := h_adic

/-- The test object `Spf(R)` of a solid adic square. -/
abbrev specSpf (sq : AdicSpfSquare f) : (Over S)ᵒᵖ ⥤ Type u :=
  @spf sq.R sq.commRing sq.domain sq.discreteValuationRing sq.completeLocalRing S sq.structureHom

/-- The structure morphism of `AdicSpfSquare.of` is the given morphism to `S`. -/
theorem of_structureHom (f : X ⟶ Y) (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsCompleteLocalRing R] (structureHom : Spec (.of R) ⟶ S)
    (p : spf R structureHom ⟶ Y)
    (h_adic : AlgebraicSpace.representableByAlgebraicSpaces p) :
    (of f R structureHom p h_adic).structureHom = structureHom :=
  rfl

/-- A solid adic `Spf` square is given by a complete discrete valuation ring
together with an adic test map from its formal spectrum. -/
theorem spec (sq : AdicSpfSquare f) :
    @IsDiscreteValuationRing sq.R sq.commRing sq.domain ∧
      @IsCompleteLocalRing sq.R sq.commRing ∧
      AlgebraicSpace.representableByAlgebraicSpaces sq.p :=
  ⟨sq.discreteValuationRing, sq.completeLocalRing, sq.h_adic⟩

/-- An extension of a solid adic `Spf` square is an extension of complete
discrete valuation rings `R ⊂ R'` together with a morphism `Spf(R') ⟶ X`
making the displayed triangle commute. -/
structure Extension (sq : AdicSpfSquare f) where
  /-- The extended complete discrete valuation ring. -/
  R' : Type u
  /-- The ring operations on the extension ring. -/
  commRing : CommRing R'
  /-- The extension ring is a domain. -/
  domain : @IsDomain R' commRing.toSemiring
  /-- The extension ring is a discrete valuation ring. -/
  discreteValuationRing : @IsDiscreteValuationRing R' commRing domain
  /-- The extension ring is complete for its maximal-adic topology. -/
  completeLocalRing : @IsCompleteLocalRing R' commRing
  /-- The algebra structure defining the extension. -/
  algebra : @Algebra sq.R R' sq.commRing.toCommSemiring commRing.toSemiring
  /-- The algebra map is an injective local map of discrete valuation rings. -/
  isExtension : @IsExtensionOfDiscreteValuationRings sq.R R' sq.commRing commRing algebra
    sq.domain sq.discreteValuationRing domain discreteValuationRing
  /-- A lift `Spf(R') ⟶ X` of the extended square. -/
  lift :
    @spf R' commRing domain discreteValuationRing completeLocalRing S
      (Spec.map (@CommRingCat.ofHom sq.R R' sq.commRing commRing
        (@algebraMap sq.R R' sq.commRing.toCommSemiring commRing.toSemiring algebra)) ≫
          sq.structureHom) ⟶ X
  /-- The displayed triangle commutes. -/
  fac : lift ≫ f = @spfMap sq.R R' sq.commRing sq.domain sq.discreteValuationRing sq.completeLocalRing
    commRing domain discreteValuationRing completeLocalRing algebra isExtension S sq.structureHom ≫ sq.p

namespace Extension

/-- Construct an extension of a solid adic `Spf` square from an extension of
complete discrete valuation rings and a commuting lift. -/
@[reducible]
def of (sq : AdicSpfSquare f) (R' : Type u) [cr : CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] [IsCompleteLocalRing R']
    [alg : @Algebra sq.R R' sq.commRing.toCommSemiring cr.toSemiring]
    [ext : @IsExtensionOfDiscreteValuationRings sq.R R' sq.commRing inferInstance alg
      sq.domain sq.discreteValuationRing inferInstance inferInstance]
    (lift : spf R'
      (Spec.map (@CommRingCat.ofHom sq.R R' sq.commRing cr
        (@algebraMap sq.R R' sq.commRing.toCommSemiring cr.toSemiring alg)) ≫
          sq.structureHom) ⟶ X)
    (fac : lift ≫ f = @spfMap sq.R R' sq.commRing sq.domain sq.discreteValuationRing sq.completeLocalRing
      inferInstance inferInstance inferInstance inferInstance alg ext S sq.structureHom ≫ sq.p) :
    sq.Extension where
  R' := R'
  commRing := inferInstance
  domain := inferInstance
  discreteValuationRing := inferInstance
  completeLocalRing := inferInstance
  algebra := alg
  isExtension := ext
  lift := lift
  fac := fac

/-- The vertical morphism `Spf(R') ⟶ Spf(R)` of an extended adic square. -/
abbrev verticalMap {sq : AdicSpfSquare f} (e : sq.Extension) :
    @spf e.R' e.commRing e.domain e.discreteValuationRing e.completeLocalRing S
      (Spec.map (@CommRingCat.ofHom sq.R e.R' sq.commRing e.commRing
        (@algebraMap sq.R e.R' sq.commRing.toCommSemiring e.commRing.toSemiring e.algebra)) ≫
          sq.structureHom) ⟶
      specSpf sq :=
  @spfMap sq.R e.R' sq.commRing sq.domain sq.discreteValuationRing sq.completeLocalRing
    e.commRing e.domain e.discreteValuationRing e.completeLocalRing e.algebra e.isExtension S
    sq.structureHom

/-- The two paths `Spf(R') ⟶ Y` of an extended adic square agree. -/
theorem spec {sq : AdicSpfSquare f} (e : sq.Extension) :
    e.lift ≫ f = e.verticalMap ≫ sq.p :=
  e.fac

/-- The lift of an extension constructed from a commuting lift is the given lift. -/
theorem of_lift (sq : AdicSpfSquare f) (R' : Type u) [cr : CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] [IsCompleteLocalRing R']
    [alg : @Algebra sq.R R' sq.commRing.toCommSemiring cr.toSemiring]
    [ext : @IsExtensionOfDiscreteValuationRings sq.R R' sq.commRing inferInstance alg
      sq.domain sq.discreteValuationRing inferInstance inferInstance]
    (lift : spf R'
      (Spec.map (@CommRingCat.ofHom sq.R R' sq.commRing cr
        (@algebraMap sq.R R' sq.commRing.toCommSemiring cr.toSemiring alg)) ≫
          sq.structureHom) ⟶ X)
    (fac : lift ≫ f = @spfMap sq.R R' sq.commRing sq.domain sq.discreteValuationRing sq.completeLocalRing
      inferInstance inferInstance inferInstance inferInstance alg ext S sq.structureHom ≫ sq.p) :
    (of sq R' lift fac).lift = lift :=
  rfl

end Extension

end AdicSpfSquare

end AlgebraicGeometry.FormalAlgebraicSpace
