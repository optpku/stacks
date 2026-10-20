/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Universal

/-!
# Relative spectrum over a scheme-valued algebraic space

Restrict the algebra to the identity scheme chart and use the actual native
scheme relative spectrum. Comma-chart section evaluation gives its algebraic
space point. Conversely, a supplied original point's actual global algebra
map evaluates on inverse-image opens and gives its native scheme spectrum
map. The resulting Yoneda isomorphism has both actual directions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry RingedSpace
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {T W : Over S}

/-- The identity étale chart of the scheme-valued base. -/
def relativeSpectrumSchemeIdentityChart (T : Over S) : smallEtaleSite (ofOver T) :=
  smallEtaleSite.mk (𝟙 (ofOver T))

/-- The native scheme algebra is restriction of the given algebra to its identity chart. -/
def relativeSpectrumSchemeAlgebra (A : (ofOver T).QcAlgebraUnder) : T.left.QcAlgebraUnder :=
  onChart A (relativeSpectrumSchemeIdentityChart T)

/-- The actual native scheme relative spectrum, composed to the original base S. -/
def relativeSpectrumSchemeOver (A : (ofOver T).QcAlgebraUnder) : Over S :=
  Over.mk ((Scheme.relativeSpectrumOver (relativeSpectrumSchemeAlgebra A)).π ≫ T.hom)

/-- The actual native structural morphism to the scheme-valued base. -/
def relativeSpectrumSchemeToBase (A : (ofOver T).QcAlgebraUnder) : relativeSpectrumSchemeOver A ⟶ T :=
  Over.homMk (Scheme.relativeSpectrumOver (relativeSpectrumSchemeAlgebra A)).π rfl

/-- Every scheme étale over the scheme-valued base has its actual map to the identity chart. -/
def relativeSpectrumSchemeChartToIdentity (U : smallEtaleSite (ofOver T)) :
    U ⟶ relativeSpectrumSchemeIdentityChart T :=
  MorphismProperty.CostructuredArrow.homMk (yoneda.preimage U.hom) trivial sorry

/-- The actual scheme map of a native-spectrum direct-image comma chart to the spectrum scheme. -/
def relativeSpectrumSchemeCommaToSpectrum (A : (ofOver T).QcAlgebraUnder)
    (U : smallEtaleSite (ofOver T))
    (a : StructuredArrow (op ((etaleBaseChange (ofOverMap (relativeSpectrumSchemeToBase A))).obj U))
      (smallEtaleToSpaces (ofOver (relativeSpectrumSchemeOver A))).op) :
    a.right.unop.left ⟶ relativeSpectrumSchemeOver A :=
  yoneda.preimage a.right.unop.hom

/-- The same comma chart's actual scheme map to the test étale chart. -/
def relativeSpectrumSchemeCommaToChart (A : (ofOver T).QcAlgebraUnder)
    (U : smallEtaleSite (ofOver T))
    (a : StructuredArrow (op ((etaleBaseChange (ofOverMap (relativeSpectrumSchemeToBase A))).obj U))
      (smallEtaleToSpaces (ofOver (relativeSpectrumSchemeOver A))).op) : a.right.unop.left ⟶ U.left :=
  yoneda.preimage (a.hom.unop.left ≫ etaleBaseChangeSnd (ofOverMap (relativeSpectrumSchemeToBase A)) U)

/-- The actual comma-chart scheme maps satisfy the given identity-chart structural triangle. -/
theorem relativeSpectrumSchemeComma_triangle (A : (ofOver T).QcAlgebraUnder)
    (U : smallEtaleSite (ofOver T))
    (a : StructuredArrow (op ((etaleBaseChange (ofOverMap (relativeSpectrumSchemeToBase A))).obj U))
      (smallEtaleToSpaces (ofOver (relativeSpectrumSchemeOver A))).op) :
    (relativeSpectrumSchemeCommaToSpectrum A U a).left ≫
        (Scheme.relativeSpectrumOver (relativeSpectrumSchemeAlgebra A)).π =
      (relativeSpectrumSchemeCommaToChart A U a).left ≫
        (relativeSpectrumSchemeChartToIdentity U).left.left := sorry

/-- Actual section evaluation over the native identity-chart relative spectrum. -/
def relativeSpectrumSchemeAlgebraCone (A : (ofOver T).QcAlgebraUnder)
    (U : smallEtaleSite (ofOver T)) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange (ofOverMap (relativeSpectrumSchemeToBase A))).obj U))
      (smallEtaleToSpaces (ofOver (relativeSpectrumSchemeOver A))).op ⋙
        (commStructureSheaf (ofOver (relativeSpectrumSchemeOver A))).obj) where
  pt := sectionRing A U
  π :=
    { app := fun a ↦ relativeSpectrumGluedPointEvaluation A (relativeSpectrumSchemeChartToIdentity U)
        (relativeSpectrumSchemeCommaToChart A U a).left (relativeSpectrumSchemeCommaToSpectrum A U a).left
        (relativeSpectrumSchemeComma_triangle A U a)
      naturality := sorry }

/-- The native scheme spectrum carries the actual global algebra map over the scheme-valued base. -/
def relativeSpectrumSchemeAlgebraMap (A : (ofOver T).QcAlgebraUnder) :
    A.obj ⟶ relativeSpectrumTarget (ofOverMap (relativeSpectrumSchemeToBase A)) :=
  Under.homMk
    ⟨{ app := fun U ↦ ConormalAlgebra.commRingPushforwardConeLift
          (ofOverMap (relativeSpectrumSchemeToBase A))
          (commStructureSheaf (ofOver (relativeSpectrumSchemeOver A))) U.unop
          (relativeSpectrumSchemeAlgebraCone A U.unop)
       naturality := sorry }⟩ sorry

/-- The actual native scheme spectrum point defines the forward Yoneda map. -/
def relativeSpectrumSchemeNat (A : (ofOver T).QcAlgebraUnder) :
    yoneda.obj (relativeSpectrumSchemeOver A) ⟶ relativeSpectrumFunctor A :=
  yonedaEquiv.symm (relativeSpectrumPairMk (ofOverMap (relativeSpectrumSchemeToBase A))
    (relativeSpectrumSchemeAlgebraMap A))

/-- A supplied original point over a scheme-valued base has its actual native scheme base arrow. -/
def relativeSpectrumSchemePointBase (A : (ofOver T).QcAlgebraUnder) (p : relativeSpectrumPair A W) :
    W ⟶ T := yoneda.preimage (relativeSpectrumPointBase A p)

/-- The actual inverse-image open subscheme is an étale chart of the point's scheme. -/
def relativeSpectrumSchemePointOpenChart (A : (ofOver T).QcAlgebraUnder)
    (p : relativeSpectrumPair A W) (P : T.left.Opens) : smallEtaleSite (ofOver W) :=
  @smallEtaleSite.mk S (ofOver W)
    (Over.mk (((relativeSpectrumSchemePointBase A p).left ⁻¹ᵁ P).ι ≫ W.hom))
    (ofOverMap (Over.homMk ((relativeSpectrumSchemePointBase A p).left ⁻¹ᵁ P).ι rfl)) sorry

/-- The inverse-image open's actual scheme map to the identity-base open. -/
def relativeSpectrumSchemePointOpenToBaseOpen (A : (ofOver T).QcAlgebraUnder)
    (p : relativeSpectrumPair A W) (P : T.left.Opens) :
    (relativeSpectrumSchemePointOpenChart A p P).left ⟶
      ((chartOpens (relativeSpectrumSchemeIdentityChart T)).obj P).left :=
  Over.homMk ((relativeSpectrumSchemePointBase A p).left ∣_ P) sorry

/-- The actual open-subscheme arrows give the evaluation arrow for the point's reconstructed map. -/
def relativeSpectrumSchemePointOpenEvaluationArrow (A : (ofOver T).QcAlgebraUnder)
    (p : relativeSpectrumPair A W) (P : T.left.Opens) :
    (smallEtaleToSpaces (ofOver W)).obj (relativeSpectrumSchemePointOpenChart A p P) ⟶
      (etaleBaseChange (relativeSpectrumPointBase A p)).obj
        ((chartOpens (relativeSpectrumSchemeIdentityChart T)).obj P) :=
  MorphismProperty.Over.homMk
    ((pullback.lift (relativeSpectrumSchemePointOpenChart A p P).hom
      (ofOverMap (relativeSpectrumSchemePointOpenToBaseOpen A p P)) sorry :
      yoneda.obj (relativeSpectrumSchemePointOpenChart A p P).left ⟶
        (etaleBaseChangeSpace (relativeSpectrumPointBase A p)
          ((chartOpens (relativeSpectrumSchemeIdentityChart T)).obj P)).functorOfPoints)) sorry

/-- Evaluate the actual point algebra map on inverse-image base opens. -/
def relativeSpectrumSchemePointSectionMap (A : (ofOver T).QcAlgebraUnder)
    (p : relativeSpectrumPair A W) (P : T.left.Opens) :
    Scheme.qcAlgebraSectionRing (relativeSpectrumSchemeAlgebra A) P ⟶
      Γ(((relativeSpectrumSchemePointBase A p).left ⁻¹ᵁ P).toScheme, ⊤) :=
  (InducedCategory.Hom.hom (relativeSpectrumPointAlgebraMap A p).right).app
      (op ((chartOpens (relativeSpectrumSchemeIdentityChart T)).obj P)) ≫
    commRingPushforwardEvaluation (relativeSpectrumPointBase A p) (commStructureSheaf (ofOver W))
      (relativeSpectrumSchemePointOpenEvaluationArrow A p P)

/-- The native Zariski algebra map comes from those actual reconstructed point values. -/
def relativeSpectrumSchemePointAlgebraMap (A : (ofOver T).QcAlgebraUnder)
    (p : relativeSpectrumPair A W) :
    (relativeSpectrumSchemeAlgebra A).obj ⟶ Under.mk
      (Hom.commRingSheafPushforwardMap (relativeSpectrumSchemePointBase A p).left.toShHom) :=
  Under.homMk
    ⟨{ app := fun P ↦ relativeSpectrumSchemePointSectionMap A p P.unop ≫
        (Scheme.Opens.topIso ((relativeSpectrumSchemePointBase A p).left ⁻¹ᵁ P.unop)).hom
       naturality := sorry }⟩ sorry

/-- The actual inverse Yoneda function is the native affine-glued spectrum point map. -/
def relativeSpectrumSchemePointMap (A : (ofOver T).QcAlgebraUnder)
    (p : relativeSpectrumPair A W) : W ⟶ relativeSpectrumSchemeOver A :=
  Over.homMk
    (Scheme.relativeSpectrumPointMap (relativeSpectrumSchemeAlgebra A)
      ⟨(relativeSpectrumSchemePointBase A p).left, relativeSpectrumSchemePointAlgebraMap A p⟩) sorry

/-- The actual pointwise native scheme map gives the inverse transformation. -/
def relativeSpectrumSchemeNatInverse (A : (ofOver T).QcAlgebraUnder) :
    relativeSpectrumFunctor A ⟶ yoneda.obj (relativeSpectrumSchemeOver A) where
  app W := TypeCat.ofHom (relativeSpectrumSchemePointMap A)
  naturality := sorry

/-- Relative spectrum over a scheme-valued base is identified with the actual native scheme model. -/
def relativeSpectrumSchemeIso (A : (ofOver T).QcAlgebraUnder) :
    yoneda.obj (relativeSpectrumSchemeOver A) ≅ relativeSpectrumFunctor A where
  hom := relativeSpectrumSchemeNat A
  inv := relativeSpectrumSchemeNatInverse A
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The scheme-spectrum identification commutes with the original base projection. -/
theorem relativeSpectrumSchemeNat_toBase (A : (ofOver T).QcAlgebraUnder) :
    NatTrans.vcomp (relativeSpectrumSchemeNat A) (homFunctor (relativeSpecπ A)) =
      yoneda.map (relativeSpectrumSchemeToBase A) := sorry

end AlgebraicGeometry.AlgebraicSpace
