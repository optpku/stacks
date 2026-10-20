/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.GradedObject
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Presentation

/-!
# Twisting comparisons for relative projective spectra

This file packages the comparison between relative projective-spectrum presentations whose
graded algebras differ by integral tensor powers of an invertible module.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {S X Y : Scheme.{u}} {p : X ⟶ S} {p' : Y ⟶ S}

/-- The degree-`n` piece of a graded algebra twisted by the `n`th integral tensor power of an
invertible module. -/
abbrev twistedAlgebraPiece
    (L : S.Modules) [Scheme.Modules.Invertible L]
    (P : RelativeProjPresentation p) (n : ℤ) : S.Modules :=
  Scheme.Modules.twistByTensorPower L (P.algebra n) n

/-- The degree-`n` relative-Proj twist tensored with the pullback of the `n`th integral tensor
power of an invertible base module. -/
abbrev twistedTwistPiece
    (P : RelativeProjPresentation p) (L : S.Modules) [Scheme.Modules.Invertible L]
    (n : ℤ) : X.Modules :=
  tensorObj (P.twist n)
    ((Scheme.Modules.pullback p).obj (Scheme.Modules.tensorPowerInt L n))

/-- The pullback of a degree-`n` relative-Proj twist along a scheme isomorphism. -/
abbrev pulledBackTwistPiece
    (P' : RelativeProjPresentation p') (iso : X ≅ Y) (n : ℤ) : X.Modules :=
  (Scheme.Modules.pullback iso.hom).obj (P'.twist n)

/-- Sections of a degree-`n` twisted algebra piece on an object of the base site. -/
abbrev twistedAlgebraSection
    (L : S.Modules) [Scheme.Modules.Invertible L]
    (P : RelativeProjPresentation p) (n : ℤ) (U : (Opens S)ᵒᵖ) :=
  (twistedAlgebraPiece L P n).val.obj U

/-- Sections of a pulled-back relative-Proj twist on an object of the source site. -/
abbrev pulledBackTwistSection
    (P' : RelativeProjPresentation p') (iso : X ≅ Y) (n : ℤ) (U : (Opens X)ᵒᵖ) :=
  (pulledBackTwistPiece P' iso n).val.obj U

/-- Sections of a relative-Proj twist tensored with a pulled-back integral tensor power. -/
abbrev twistedTwistSection
    (P : RelativeProjPresentation p) (L : S.Modules) [Scheme.Modules.Invertible L]
    (n : ℤ) (U : (Opens X)ᵒᵖ) :=
  (twistedTwistPiece P L n).val.obj U

/-- Sections of the sheaf-level twisted algebra piece over a base open. -/
abbrev twistedAlgebraPieceOpenSections
    (L : S.Modules) [Scheme.Modules.Invertible L]
    (P : RelativeProjPresentation p) (n : ℤ) (V : Opens S) : AddCommGrpCat :=
  RingedSpace.moduleSectionsOnOpen (twistedAlgebraPiece L P n) V

/-- The tensor product of the degree-`n` algebra sections and the integral tensor-power sections
over the ring of functions on a base open. -/
abbrev twistedAlgebraOpenSections
    (L : S.Modules) [Scheme.Modules.Invertible L]
    (P : RelativeProjPresentation p) (n : ℤ) (V : Opens S) : AddCommGrpCat :=
  AddCommGrpCat.of
    (TensorProduct (S.presheaf.obj (op V))
      ((P.algebra n).val.obj (op V))
      ((Scheme.Modules.tensorPowerInt L n).val.obj (op V)))

/-- The tensor product of twist sections and pulled-back tensor-power sections over the ring of
functions on the inverse image of a base open. -/
abbrev twistedTwistFactorOpenSections
    (P : RelativeProjPresentation p) (L : S.Modules) [Scheme.Modules.Invertible L]
    (n : ℤ) (V : Opens S) : AddCommGrpCat :=
  AddCommGrpCat.of
    (TensorProduct (X.presheaf.obj (op (p ⁻¹ᵁ V)))
      ((P.twist n).val.obj (op (p ⁻¹ᵁ V)))
      (((Scheme.Modules.pullback p).obj (Scheme.Modules.tensorPowerInt L n)).val.obj
        (op (p ⁻¹ᵁ V))))

/-- The canonical map from a tensor product of local sections to sections of the corresponding
twisted algebra piece. -/
noncomputable def twistedAlgebraPieceSectionMap
    (L : S.Modules) [Scheme.Modules.Invertible L]
    (P : RelativeProjPresentation p) (n : ℤ) (V : Opens S) :
    twistedAlgebraOpenSections L P n V ⟶
      twistedAlgebraPieceOpenSections L P n V :=
  AddCommGrpCat.ofHom
    (TensorProduct.lift
      (SheafOfModules.RingedSite.tensorSectionLinear S.sheaf (P.algebra n)
        (Scheme.Modules.tensorPowerInt L n) (op V))).toAddMonoidHom

/-- Sections of a pulled-back relative-Proj twist over the inverse image of a base open. -/
abbrev pulledBackTwistOpenSections
    (P' : RelativeProjPresentation p') (iso : X ≅ Y) (n : ℤ) (V : Opens S) :
    AddCommGrpCat :=
  RingedSpace.moduleSectionsOnOpen (pulledBackTwistPiece P' iso n) (p ⁻¹ᵁ V)

/-- Sections of a relative-Proj twist tensored with a pulled-back tensor power over the inverse
image of a base open. -/
abbrev twistedTwistOpenSections
    (P : RelativeProjPresentation p) (L : S.Modules) [Scheme.Modules.Invertible L]
    (n : ℤ) (V : Opens S) : AddCommGrpCat :=
  RingedSpace.moduleSectionsOnOpen (twistedTwistPiece P L n) (p ⁻¹ᵁ V)

/-- The canonical map from the tensor product of the two factorwise section modules to sections
of their tensor-product sheaf. -/
noncomputable def twistedTwistFactorSectionMap
    (P : RelativeProjPresentation p) (L : S.Modules) [Scheme.Modules.Invertible L]
    (n : ℤ) (V : Opens S) :
    twistedTwistFactorOpenSections P L n V ⟶ twistedTwistOpenSections P L n V :=
  AddCommGrpCat.ofHom
    (TensorProduct.lift
      (SheafOfModules.RingedSite.tensorSectionLinear X.sheaf (P.twist n)
        ((Scheme.Modules.pullback p).obj (Scheme.Modules.tensorPowerInt L n))
        (op (p ⁻¹ᵁ V)))).toAddMonoidHom

/-- Explicit algebra-side twisting data for two relative projective-spectrum presentations.
It records the degreewise algebra identifications, their graded algebra laws, and the factorwise
map on sections over every base open. -/
structure RelativeProjPresentationTwist
    (P : RelativeProjPresentation p) (P' : RelativeProjPresentation p')
    (L : S.Modules) [Scheme.Modules.Invertible L] where
  /-- The degree-`n` twisted source algebra piece is identified with the target algebra piece. -/
  algebraIso : ∀ n : ℤ, twistedAlgebraPiece L P n ≅ P'.algebra n
  /-- Multiplication on sections of the twisted source algebra pieces. -/
  twistedMul :
    ∀ (U : (Opens S)ᵒᵖ) (n m : ℤ),
      twistedAlgebraSection L P n U →ₗ[S.presheaf.obj U]
        twistedAlgebraSection L P m U →ₗ[S.presheaf.obj U]
          twistedAlgebraSection L P (n + m) U
  /-- The unit section of the degree-zero twisted source algebra piece. -/
  twistedOne : ∀ U : (Opens S)ᵒᵖ, twistedAlgebraSection L P 0 U
  /-- The degreewise identification preserves the degree-zero unit. -/
  map_one :
    ∀ U : (Opens S)ᵒᵖ,
      (((algebraIso 0).hom.val.app U).hom) (twistedOne U) = P'.algebra.one U
  /-- The degreewise identifications preserve graded multiplication. -/
  map_mul :
    ∀ (U : (Opens S)ᵒᵖ) (n m : ℤ)
      (a : twistedAlgebraSection L P n U)
      (b : twistedAlgebraSection L P m U),
      (((algebraIso (n + m)).hom.val.app U).hom) (twistedMul U n m a b) =
        P'.algebra.mul U n m ((((algebraIso n).hom.val.app U).hom) a)
          ((((algebraIso m).hom.val.app U).hom) b)
  /-- The factorwise vertical map from the tensor product of base sections to the tensor product
  of sections over the inverse-image open. -/
  factorSectionMap :
    ∀ (V : Opens S) (n : ℤ),
      twistedAlgebraOpenSections L P n V ⟶ twistedTwistFactorOpenSections P L n V

namespace RelativeProjPresentationTwist

/-- The section map obtained by applying the factorwise vertical map and then the canonical
tensor-section map. -/
noncomputable def sectionMap
    {P : RelativeProjPresentation p} {P' : RelativeProjPresentation p'}
    {L : S.Modules} [Scheme.Modules.Invertible L]
    (hTwist : RelativeProjPresentationTwist P P' L) (V : Opens S) (n : ℤ) :
    twistedAlgebraOpenSections L P n V ⟶ twistedTwistOpenSections P L n V :=
  hTwist.factorSectionMap V n ≫ twistedTwistFactorSectionMap P L n V

/-- The top horizontal map on sections, obtained from the canonical tensor-section map followed
by the degreewise algebra identification. -/
noncomputable def algebraSectionMap
    {P : RelativeProjPresentation p} {P' : RelativeProjPresentation p'}
    {L : S.Modules} [Scheme.Modules.Invertible L]
    (hTwist : RelativeProjPresentationTwist P P' L) (V : Opens S) (n : ℤ) :
    twistedAlgebraOpenSections L P n V ⟶
      RingedSpace.moduleSectionsOnOpen (P'.algebra n) V :=
  twistedAlgebraPieceSectionMap L P n V ≫
    RingedSpace.moduleSectionsMapOnOpen ((hTwist.algebraIso n).hom) V

/-- The degreewise algebra identifications preserve both the degree-zero unit and graded
multiplication. -/
theorem algebraCompatibility_spec
    {P : RelativeProjPresentation p} {P' : RelativeProjPresentation p'}
    {L : S.Modules} [Scheme.Modules.Invertible L]
    (hTwist : RelativeProjPresentationTwist P P' L) :
    (∀ U : (Opens S)ᵒᵖ,
      ((((hTwist.algebraIso 0).hom.val.app U).hom) (hTwist.twistedOne U)) =
        P'.algebra.one U) ∧
      ∀ (U : (Opens S)ᵒᵖ) (n m : ℤ)
        (a : twistedAlgebraSection L P n U)
        (b : twistedAlgebraSection L P m U),
        ((((hTwist.algebraIso (n + m)).hom.val.app U).hom)
            (hTwist.twistedMul U n m a b)) =
          P'.algebra.mul U n m
            ((((hTwist.algebraIso n).hom.val.app U).hom) a)
            ((((hTwist.algebraIso m).hom.val.app U).hom) b) := sorry

end RelativeProjPresentationTwist

/-- Explicit comparison data for relative projective-spectrum presentations whose graded
algebras differ by integral tensor powers of an invertible module. The degreewise twist
isomorphisms preserve units, multiplication, and the canonical section diagram. -/
structure RelativeProjPresentationTwistComparison
    (P : RelativeProjPresentation p) (P' : RelativeProjPresentation p') (L : S.Modules)
    [Scheme.Modules.Invertible L] (hTwist : RelativeProjPresentationTwist P P' L) where
  /-- The comparison isomorphism of the source schemes. -/
  iso : X ≅ Y
  /-- The comparison isomorphism lies over the base scheme. -/
  comm : iso.hom ≫ p' = p
  /-- The pullback of every target twist is identified with the corresponding twisted source
  twist. -/
  theta : ∀ n : ℤ, pulledBackTwistPiece P' iso n ≅ twistedTwistPiece P L n
  /-- The section map from a target algebra piece to the pulled-back target twist. -/
  pullbackSectionMap :
    ∀ (V : Opens S) (n : ℤ),
      RingedSpace.moduleSectionsOnOpen (P'.algebra n) V ⟶
        pulledBackTwistOpenSections P' iso n V
  /-- The degree-zero unit section of the pulled-back twist family. -/
  pullbackOne : ∀ U : (Opens X)ᵒᵖ, pulledBackTwistSection P' iso 0 U
  /-- The degree-zero unit section of the twisted source family. -/
  twistedOne : ∀ U : (Opens X)ᵒᵖ, twistedTwistSection P L 0 U
  /-- Graded multiplication on sections of the pulled-back twist family. -/
  pullbackMul :
    ∀ (U : (Opens X)ᵒᵖ) (n m : ℤ),
      pulledBackTwistSection P' iso n U →ₗ[X.presheaf.obj U]
        pulledBackTwistSection P' iso m U →ₗ[X.presheaf.obj U]
          pulledBackTwistSection P' iso (n + m) U
  /-- Graded multiplication on sections of the twisted source family. -/
  twistedMul :
    ∀ (U : (Opens X)ᵒᵖ) (n m : ℤ),
      twistedTwistSection P L n U →ₗ[X.presheaf.obj U]
        twistedTwistSection P L m U →ₗ[X.presheaf.obj U]
          twistedTwistSection P L (n + m) U
  /-- The degreewise comparison makes the complete section diagram commute on every base open. -/
  degreeCommutes :
    ∀ (V : Opens S) (n : ℤ),
      hTwist.algebraSectionMap V n ≫ pullbackSectionMap V n ≫
          RingedSpace.moduleSectionsMapOnOpen ((theta n).hom) (p ⁻¹ᵁ V) =
        hTwist.sectionMap V n
  /-- The degree-zero comparison carries the pulled-back unit to the twisted source unit. -/
  thetaMapOne :
    ∀ U : (Opens X)ᵒᵖ,
      (((theta 0).hom.val.app U).hom) (pullbackOne U) = twistedOne U
  /-- The degreewise comparison preserves graded multiplication on sections. -/
  thetaMapMul :
    ∀ (U : (Opens X)ᵒᵖ) (n m : ℤ)
      (a : pulledBackTwistSection P' iso n U)
      (b : pulledBackTwistSection P' iso m U),
      (((theta (n + m)).hom.val.app U).hom) (pullbackMul U n m a b) =
        (twistedMul U n m)
          ((((theta n).hom.val.app U).hom) a)
          ((((theta m).hom.val.app U).hom) b)

/-- Twisting every graded algebra piece by the corresponding integral tensor power of an
invertible base module yields a comparison of the associated relative projective spectra. -/
theorem relativeProjPresentationTwistComparisonExists
    (P : RelativeProjPresentation p) (P' : RelativeProjPresentation p')
    (L : S.Modules) [Scheme.Modules.Invertible L]
    (hTwist : RelativeProjPresentationTwist P P' L) :
    ∃ hComparison : RelativeProjPresentationTwistComparison P P' L hTwist,
      hComparison.iso.hom ≫ p' = p ∧
        ∀ n : ℤ,
          Nonempty
            (pulledBackTwistPiece P' hComparison.iso n ≅ twistedTwistPiece P L n) := sorry

namespace RelativeProjPresentationTwistComparison

/-- The comparison lies over the base, commutes with the section maps in every degree, and
preserves the degree-zero unit and graded multiplication. -/
theorem compatibility_spec
    {P : RelativeProjPresentation p} {P' : RelativeProjPresentation p'}
    {L : S.Modules} [Scheme.Modules.Invertible L]
    {hTwist : RelativeProjPresentationTwist P P' L}
    (hComparison : RelativeProjPresentationTwistComparison P P' L hTwist) :
    hComparison.iso.hom ≫ p' = p ∧
      (∀ (V : Opens S) (n : ℤ),
        hTwist.algebraSectionMap V n ≫ hComparison.pullbackSectionMap V n ≫
            RingedSpace.moduleSectionsMapOnOpen ((hComparison.theta n).hom) (p ⁻¹ᵁ V) =
          hTwist.sectionMap V n) ∧
        (∀ U : (Opens X)ᵒᵖ,
          ((((hComparison.theta 0).hom.val.app U).hom) (hComparison.pullbackOne U)) =
            hComparison.twistedOne U) ∧
          ∀ (U : (Opens X)ᵒᵖ) (n m : ℤ)
            (a : pulledBackTwistSection P' hComparison.iso n U)
            (b : pulledBackTwistSection P' hComparison.iso m U),
            ((((hComparison.theta (n + m)).hom.val.app U).hom)
                (hComparison.pullbackMul U n m a b)) =
              hComparison.twistedMul U n m
                ((((hComparison.theta n).hom.val.app U).hom) a)
                ((((hComparison.theta m).hom.val.app U).hom) b) := sorry

/-- The pulled-back twist family viewed as an integer-graded object. -/
abbrev pulledBackTwistGraded
    {P' : RelativeProjPresentation p'} (iso : X ≅ Y) :
    CategoryTheory.GradedObject ℤ X.Modules :=
  fun n ↦ pulledBackTwistPiece P' iso n

/-- The source twist family tensored with pulled-back integral tensor powers, viewed as an
integer-graded object. -/
abbrev twistedTwistGraded
    {P : RelativeProjPresentation p}
    {L : S.Modules} [Scheme.Modules.Invertible L] :
    CategoryTheory.GradedObject ℤ X.Modules :=
  fun n ↦ twistedTwistPiece P L n

/-- The degreewise twist comparisons bundled as an isomorphism of integer-graded objects. -/
noncomputable def thetaGradedIso
    {P : RelativeProjPresentation p} {P' : RelativeProjPresentation p'}
    {L : S.Modules} [Scheme.Modules.Invertible L]
    {hTwist : RelativeProjPresentationTwist P P' L}
    (hComparison : RelativeProjPresentationTwistComparison P P' L hTwist) :
    pulledBackTwistGraded (P' := P') hComparison.iso ≅
      twistedTwistGraded (P := P) (L := L) :=
  CategoryTheory.GradedObject.isoMk _ _ hComparison.theta

/-- The degree-`n` component of the bundled graded isomorphism is the original degreewise
comparison map. -/
theorem thetaGradedIso_hom_app
    {P : RelativeProjPresentation p} {P' : RelativeProjPresentation p'}
    {L : S.Modules} [Scheme.Modules.Invertible L]
    {hTwist : RelativeProjPresentationTwist P P' L}
    (hComparison : RelativeProjPresentationTwistComparison P P' L hTwist) (n : ℤ) :
    (thetaGradedIso hComparison).hom n = (hComparison.theta n).hom := sorry

end RelativeProjPresentationTwistComparison

end AlgebraicGeometry.Scheme.Hom
