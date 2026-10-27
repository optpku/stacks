/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.ReesProj
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.RelativeProj
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.ExtensionComposition
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CanonicalAlgebra
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.CategoryTheory.Yoneda

/-!
# Affine étale comparison for algebraic-space blowups

Homogeneous sections give ratio maps on nonvanishing loci. Gluing these maps
constructs the canonical comparison from the fibre product to the Rees projective scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {I : IdealSubobject X} [IsQuasiCoherent I]


private theorem chartTopMapInv_over_w (U : affineEtaleSite X) :
    (Scheme.topIso U.obj.left.left).inv ≫
      (Modules.RestrictToScheme.siteObject U.obj.left ⊤).left.hom = U.obj.left.hom := sorry

private theorem chartTopMapInv_w (U : affineEtaleSite X) :
    ofOverMap (Over.homMk (Scheme.topIso U.obj.left.left).inv
      (chartTopMapInv_over_w U)) ≫
        ((Modules.restrictPostcompose U.obj.hom).obj
          (Modules.RestrictToScheme.siteObject U.obj.left ⊤)).hom = U.obj.hom := sorry

/-- The inverse of the top-open inclusion gives a morphism of étale chart objects. -/
private def chartTopMapInv (U : affineEtaleSite X) :
    U.obj ⟶ (Modules.restrictPostcompose U.obj.hom).obj
        (Modules.RestrictToScheme.siteObject U.obj.left ⊤) :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk (Scheme.topIso U.obj.left.left).inv (chartTopMapInv_over_w U))
    trivial (chartTopMapInv_w U)

/-- The actual nth ideal-power module restricted to the affine chart. -/
private abbrev chartPowerModule (U : affineEtaleSite X) (n : ℕ) : U.obj.left.left.Modules :=
  (Modules.restrictToScheme U.obj.left).obj ((Modules.pullback U.obj.hom).obj (I.pow n).toModule)

/-- A restricted ideal-power section determines a section on the original affine étale object. -/
private def chartPowerSection (U : affineEtaleSite X) (n : ℕ)
    (s : Γ(chartPowerModule (I := I) U n, ⊤)) :
    (I.pow n).toModule.val.obj (op U.obj) :=
  (I.pow n).toModule.val.map (chartTopMapInv U).op
    (((@Modules.restrictIsoPullback S (ofOver U.obj.left) X
      (I.pow n).toModule U.obj.hom U.obj.prop).inv.val.app
      (op (Modules.RestrictToScheme.siteObject U.obj.left ⊤))).hom
      (Modules.RestrictToScheme.sectionEquiv U.obj.left
        ((Modules.pullback U.obj.hom).obj (I.pow n).toModule) ⊤ s))

/-- The coefficient of a power section is its image under the original ideal inclusion. -/
private def chartPowerCoefficient (U : affineEtaleSite X) (n : ℕ)
    (s : Γ(chartPowerModule (I := I) U n, ⊤)) : Γ(U.obj.left.left, ⊤) :=
  ((I.pow n).arrow.val.app (op U.obj)).hom (chartPowerSection U n s)

/-- On an affine chart a quasi-coherent ideal-power section has coefficient in I_A^n. -/
private theorem chartPowerCoefficient_mem (U : affineEtaleSite X) (n : ℕ)
    (s : Γ(chartPowerModule (I := I) U n, ⊤)) :
    chartPowerCoefficient U n s ∈ correspondingIdeal I U ^ n := sorry

private theorem chartPowerCoefficient_zero (U : affineEtaleSite X) (n : ℕ) :
    chartPowerCoefficient (I := I) U n 0 = 0 := sorry

private theorem chartPowerCoefficient_add (U : affineEtaleSite X) (n : ℕ)
    (s t : Γ(chartPowerModule (I := I) U n, ⊤)) :
    chartPowerCoefficient U n (s + t) =
      chartPowerCoefficient U n s + chartPowerCoefficient U n t := sorry

/-- The fixed coefficient map, with the actual ideal inclusion as its underlying function. -/
private def chartPowerCoefficientHom (U : affineEtaleSite X) (n : ℕ) :
    Γ(chartPowerModule (I := I) U n, ⊤) →+ ↥(correspondingIdeal I U ^ n) where
  toFun s := ⟨chartPowerCoefficient U n s, chartPowerCoefficient_mem U n s⟩
  map_zero' := Subtype.ext (chartPowerCoefficient_zero U n)
  map_add' s t := Subtype.ext (chartPowerCoefficient_add U n s t)

/-- Affine quasi-coherence identifies the fixed coefficient map with I_A^n.
This inverts only the given module inclusion onto its specified coefficient image. -/
private theorem chartPowerCoefficientHom_bijective (U : affineEtaleSite X) (n : ℕ) :
    Function.Bijective (chartPowerCoefficientHom (I := I) U n) := sorry

/-- The section with a specified ideal-power coefficient. -/
private def sectionOfPowerCoefficient (U : affineEtaleSite X) (n : ℕ)
    (a : ↥(correspondingIdeal I U ^ n)) : Γ(chartPowerModule (I := I) U n, ⊤) :=
  (Equiv.ofBijective (chartPowerCoefficientHom U n)
    (chartPowerCoefficientHom_bijective U n)).symm a

/-- The nth Rees twist pulled back to a test scheme. -/
private abbrev testTwist (π : Blowup X I) {T : Over S} (x : ofOver T ⟶ π.space) (n : ℕ) :
    T.left.Modules :=
  (Modules.restrictToScheme T).obj ((Modules.pullback x).obj (π.reesTwist.twistModule n))

/-- The actual homogeneous canonical map after pullback, with only base-triangle transport. -/
private def testHomogeneousMap (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (q : T ⟶ U.obj.left) (x : ofOver T ⟶ π.space)
    (w : ofOverMap q ≫ U.obj.hom = x ≫ π.hom) (n : ℕ) :
    (Scheme.Modules.pullback q.left).obj (chartPowerModule (I := I) U n) ⟶ testTwist π x n :=
  Modules.RestrictToScheme.compositePullbackComparison U.obj.hom q (I.pow n).toModule ≫
    (Modules.restrictToScheme T).map
      (eqToHom (congrArg (fun a ↦ (Modules.pullback a).obj (I.pow n).toModule) w) ≫
        (Modules.pullbackCompIso x π.hom).inv.app (I.pow n).toModule ≫
          (Modules.pullback x).map (π.reesTwist.canonicalHom n))

/-- The homogeneous section with coefficient a is obtained from the given canonical map. -/
private def testHomogeneousSection (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (q : T ⟶ U.obj.left) (x : ofOver T ⟶ π.space)
    (w : ofOverMap q ≫ U.obj.hom = x ≫ π.hom) (n : ℕ)
    (a : ↥(correspondingIdeal I U ^ n)) : Γ(testTwist π x n, ⊤) :=
  (Scheme.Modules.globalSectionsMap (testHomogeneousMap π U q x w n)).hom
    ((Scheme.Modules.globalSectionsPullback q.left (chartPowerModule (I := I) U n)).hom
      (sectionOfPowerCoefficient U n a))

/-- Every pulled-back Rees twist is an invertible module. -/
private theorem testTwist_invertible (π : Blowup X I) {T : Over S}
    (x : ofOver T ⟶ π.space) (n : ℕ) : Scheme.Modules.Invertible (testTwist π x n) :=
  sorry

/-- The actual section corresponding to a in I_A. -/
private def testGeneratorSection (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (q : T ⟶ U.obj.left) (x : ofOver T ⟶ π.space)
    (w : ofOverMap q ≫ U.obj.hom = x ≫ π.hom) (a : correspondingIdeal I U) :
    Γ(testTwist π x 1, ⊤) :=
  testHomogeneousSection π U q x w 1 ⟨a.1, by simpa using a.2⟩

/-- The open where the actual image of a generates O(1). -/
private def generatorOpen (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (q : T ⟶ U.obj.left) (x : ofOver T ⟶ π.space)
    (w : ofOverMap q ≫ U.obj.hom = x ≫ π.hom) (a : correspondingIdeal I U) : T.left.Opens :=
  (testTwist_invertible π x 1).sectionNonvanishingOpen (testGeneratorSection π U q x w a)

section Ratios

variable (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
variable (q : T ⟶ U.obj.left) (x : ofOver T ⟶ π.space)
variable (w : ofOverMap q ≫ U.obj.hom = x ≫ π.hom)

/-- The actual degree-one line on the open where a generates it. -/
private abbrev ratioLine (a : correspondingIdeal I U) :=
  (testTwist π x 1).over (generatorOpen π U q x w a)

/-- The displayed section a gives the actual trivialization O→L on D(a). -/
private def ratioDenominator (a : correspondingIdeal I U) :
    SheafOfModules.unit (T.left.ringCatSheaf.over (generatorOpen π U q x w a)) ⟶
      ratioLine π U q x w a :=
  RingedSpace.sectionOverHom T.left.toRingedSpace (testTwist π x 1)
    (RingedSpace.sectionFromTop (testTwist π x 1) (testGeneratorSection π U q x w a))
    (generatorOpen π U q x w a)

/-- The denominator section is an isomorphism on its nonvanishing locus. -/
private theorem ratioDenominator_isIso (a : correspondingIdeal I U) :
    IsIso (ratioDenominator π U q x w a) :=
  sorry

/-- The ratio of two generator sections on the nonvanishing locus of the denominator. -/
private def ratioValue (a b : correspondingIdeal I U) :
    Γ((generatorOpen π U q x w a).toScheme, ⊤) :=
  ((generatorOpen π U q x w a).topIso.inv).hom
    (((@inv _ _ _ _ (ratioDenominator π U q x w a)
        (ratioDenominator_isIso π U q x w a)).val.app
        (op (Over.mk (𝟙 (generatorOpen π U q x w a))))).hom
    (((ratioLine π U q x w a).unitHomEquiv
      (RingedSpace.sectionOverHom T.left.toRingedSpace (testTwist π x 1)
        (RingedSpace.sectionFromTop (testTwist π x 1) (testGeneratorSection π U q x w b))
        (generatorOpen π U q x w a))).1
          (op (Over.mk (𝟙 (generatorOpen π U q x w a))))))

/-- The polynomial presentation uses every actual ideal generator, X_b↦b*t. -/
private def polynomialToRees :
    MvPolynomial (correspondingIdeal I U) Γ(U.obj.left.left, ⊤) →+*
      _root_.reesAlgebra (correspondingIdeal I U) :=
  MvPolynomial.eval₂Hom (algebraMap _ _) (ReesAlgebra.Grading.degreeOne (correspondingIdeal I U))

/-- The Rees algebra is generated by its degree-zero coefficients and degree-one monomials. -/
private theorem polynomialToRees_surjective :
    Function.Surjective (polynomialToRees (I := I) U) := sorry

/-- The actual polynomial evaluation sends b to s_b/s_a and pulls back base functions. -/
private def polynomialRatios (a : correspondingIdeal I U) :
    MvPolynomial (correspondingIdeal I U) Γ(U.obj.left.left, ⊤) →+*
      Γ((generatorOpen π U q x w a).toScheme, ⊤) :=
  MvPolynomial.eval₂Hom (((generatorOpen π U q x w a).ι ≫ q.left).appTop).hom
    (ratioValue π U q x w a)

/-- On the supplied affine Serre charts the ratios are b/a. Thus every relation
among b*t in the Rees algebra vanishes for this specific polynomial evaluation. -/
private theorem polynomialRatios_killsKer (a : correspondingIdeal I U) :
    RingHom.ker (polynomialToRees (I := I) U) ≤
      RingHom.ker (polynomialRatios π U q x w a) := sorry

/-- The ratio evaluation descended through the surjective polynomial presentation of the Rees algebra. -/
private def ratioRingHom (a : correspondingIdeal I U) :
    _root_.reesAlgebra (correspondingIdeal I U) →+* Γ((generatorOpen π U q x w a).toScheme, ⊤) :=
  (polynomialToRees (I := I) U).liftOfSurjective
    (polynomialToRees_surjective (I := I) U)
    ⟨polynomialRatios π U q x w a, polynomialRatios_killsKer π U q x w a⟩

/-- The descended ring map evaluates every polynomial by the original ratio formula. -/
private theorem ratioRingHom_polynomial (a : correspondingIdeal I U)
    (p : MvPolynomial (correspondingIdeal I U) Γ(U.obj.left.left, ⊤)) :
    ratioRingHom π U q x w a (polynomialToRees (I := I) U p) =
      polynomialRatios π U q x w a p :=
  RingHom.liftOfSurjective_comp_apply _ _
    ⟨polynomialRatios π U q x w a, polynomialRatios_killsKer π U q x w a⟩ p

/-- In particular the actual homogeneous generator b*t is sent to s_b/s_a. -/
private theorem ratioRingHom_degreeOne (a b : correspondingIdeal I U) :
    ratioRingHom π U q x w a (ReesAlgebra.Grading.degreeOne (correspondingIdeal I U) b) =
      ratioValue π U q x w a b := by
  simpa [polynomialToRees, polynomialRatios] using
    ratioRingHom_polynomial π U q x w a (MvPolynomial.X b)

/-- The ratio evaluation maps the irrelevant ideal onto the unit ideal. -/
private theorem ratioRingHom_irrelevant (a : correspondingIdeal I U) :
    (HomogeneousIdeal.irrelevant (ReesAlgebra.Grading.grade (correspondingIdeal I U))).toIdeal.map
      (ratioRingHom π U q x w a) = ⊤ := sorry

/-- The genuine local morphism is Mathlib's homogeneous-localization construction. -/
private def ratioChartMap (a : correspondingIdeal I U) :
    (generatorOpen π U q x w a).toScheme ⟶ reesProj I U :=
  Proj.fromOfGlobalSections (ReesAlgebra.Grading.grade (correspondingIdeal I U))
    (ratioRingHom π U q x w a) (ratioRingHom_irrelevant π U q x w a)

/-- The supplied degree-one Serre quotient makes the specified nonvanishing opens a cover. -/
private theorem generatorOpen_covers :
    iSup (generatorOpen π U q x w) = ⊤ := sorry

/-- The cover is built from the nonvanishing loci of actual canonical degree-one sections. -/
private def generatorCover : T.left.OpenCover :=
  T.left.openCoverOfIsOpenCover (generatorOpen π U q x w) (generatorOpen_covers π U q x w)

/-- Changing the nonvanishing generator rescales the degree-one coordinates by a unit. -/
private theorem ratioChartMap_compatible (a b : correspondingIdeal I U) :
    pullback.fst ((generatorCover π U q x w).f a) ((generatorCover π U q x w).f b) ≫
        ratioChartMap π U q x w a =
      pullback.snd ((generatorCover π U q x w).f a) ((generatorCover π U q x w).f b) ≫
        ratioChartMap π U q x w b := sorry

/-- The scheme morphism obtained by gluing the local Rees-ratio morphisms. -/
private def comparisonSchemeMap : T.left ⟶ reesProj I U :=
  (generatorCover π U q x w).glueMorphisms (ratioChartMap π U q x w)
    (ratioChartMap_compatible π U q x w)

/-- The polynomial coefficient map gives the original structure map to U. -/
private theorem comparisonSchemeMap_over :
    comparisonSchemeMap π U q x w ≫ reesProjToU I U = q.left := sorry

/-- The glued comparison as a morphism over the base scheme. -/
private def comparisonOverMap : T ⟶ reesProjOver I U :=
  Over.homMk (comparisonSchemeMap π U q x w) (by
    change comparisonSchemeMap π U q x w ≫ (reesProjToU I U ≫ U.obj.left.hom) = T.hom
    rw [← Category.assoc, comparisonSchemeMap_over π U q x w]
    exact q.w)

end Ratios


/-- Test points of the actual fibre product. -/
private abbrev affineFibrePoint (π : Blowup X I) (U : affineEtaleSite X) (T : Over S) :=
  (pullback U.obj.hom π.hom).functorOfPoints.obj (op T)

/-- The first projection gives the actual scheme map to the input chart. -/
private def affineFibrePointToU (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (p : affineFibrePoint π U T) : T ⟶ U.obj.left :=
  (pullback.fst U.obj.hom π.hom).app (op T) p

/-- The second projection gives the actual map of the test scheme into the supplied blowup. -/
private def affineFibrePointToBlowup (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (p : affineFibrePoint π U T) : ofOver T ⟶ π.space :=
  yonedaEquiv.symm ((pullback.snd U.obj.hom π.hom).app (op T) p)

/-- The two test maps satisfy the pullback triangle. -/
private theorem affineFibrePoint_triangle (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (p : affineFibrePoint π U T) :
    ofOverMap (affineFibrePointToU π U p) ≫ U.obj.hom =
      affineFibrePointToBlowup π U p ≫ π.hom := sorry

/-- The image of a test point is the scheme morphism glued from the actual Rees ratios. -/
private def affineComparisonPoint (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (p : affineFibrePoint π U T) : T ⟶ reesProjOver I U :=
  comparisonOverMap π U (affineFibrePointToU π U p) (affineFibrePointToBlowup π U p)
    (affineFibrePoint_triangle π U p)

/-- Restriction of a test point restricts all section ratios and hence the glued morphism. -/
private theorem affineComparisonPoint_naturality (π : Blowup X I) (U : affineEtaleSite X)
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (pullback U.obj.hom π.hom).functorOfPoints.map f ≫
        TypeCat.ofHom (affineComparisonPoint π U (T := T'.unop)) =
      TypeCat.ofHom (affineComparisonPoint π U (T := T.unop)) ≫
        (ofOver (reesProjOver I U)).functorOfPoints.map f := sorry

/-- The canonical affine-etale comparison has actual homogeneous-fraction morphism data. -/
@[no_expose] def affineComparisonHom (π : Blowup X I) (U : affineEtaleSite X) :
    pullback U.obj.hom π.hom ⟶ ofOver (reesProjOver I U) where
  app T := TypeCat.ofHom (affineComparisonPoint π U)
  naturality _ _ f := affineComparisonPoint_naturality π U f


/-- The specified homogeneous-fraction comparison commutes with the projection to U. -/
theorem affineComparisonHom_over (π : Blowup X I) (U : affineEtaleSite X) :
    affineComparisonHom π U ≫ reesProjOverToU I U = pullback.fst U.obj.hom π.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
