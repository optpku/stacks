/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_17_2_ReesProj
public import stacks_project.Chap71.Definition_71_17_1_Blowup
public import stacks_project.Chap71.Lemma_71_11_2_RestrictionComposition
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.AffineSectionMap
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CanonicalAlgebra
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing
open SheafOfModules.RingedSite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Blowup
variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {I : IdealSubobject X} [IsQuasiCoherent I]


/-- The original degree-one ideal module restricted to the specified affine chart. -/
abbrev chartIdealModule (U : affineEtaleSite X) : U.obj.left.left.Modules :=
  (Modules.restrictToScheme U.obj.left).obj ((Modules.pullback U.obj.hom).obj (I.pow 1).toModule)

/-- The exact degree-one twist pulled back along the given test morphism. -/
abbrev testLine (π : Blowup X I) {T : Over S} (x : ofOver T ⟶ π.space) :
    T.left.Modules :=
  (Modules.restrictToScheme T).obj ((Modules.pullback x).obj (π.reesTwist.twistModule 1))

/-- Pull back the actual canonical degree-one quotient, with its base morphism fixed. -/
def testQuotient (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (q : T ⟶ U.obj.left) (x : ofOver T ⟶ π.space)
    (w : ofOverMap q ≫ U.obj.hom = x ≫ π.hom) :
    (Scheme.Modules.pullback q.left).obj (chartIdealModule (I := I) U) ⟶
      testLine π x :=
  Modules.RestrictToScheme.compositePullbackComparison U.obj.hom q (I.pow 1).toModule ≫
    (Modules.restrictToScheme T).map
      (eqToHom (congrArg (fun a ↦ (Modules.pullback a).obj (I.pow 1).toModule) w) ≫
        (Modules.pullbackCompIso x π.hom).inv.app (I.pow 1).toModule ≫
          (Modules.pullback x).map (π.reesTwist.canonicalHom 1))

/-- The chart's top-open étale object maps to the original chart by the top inclusion. -/
def chartTopMap (U : affineEtaleSite X) :
    (Modules.restrictPostcompose U.obj.hom).obj
        (Modules.RestrictToScheme.siteObject U.obj.left ⊤) ⟶ U.obj :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk (Scheme.topIso U.obj.left.left).hom sorry) trivial sorry

/-- The inverse top inclusion has its actual scheme morphism. -/
def chartTopMapInv (U : affineEtaleSite X) :
    U.obj ⟶ (Modules.restrictPostcompose U.obj.hom).obj
        (Modules.RestrictToScheme.siteObject U.obj.left ⊤) :=
  MorphismProperty.CostructuredArrow.homMk
    (Over.homMk (Scheme.topIso U.obj.left.left).inv sorry) trivial sorry

/-- Read a section of the restricted ideal back on the original affine chart. -/
def chartIdealSection (U : affineEtaleSite X)
    (s : Γ(chartIdealModule (I := I) U, ⊤)) :
    (I.pow 1).toModule.val.obj (op U.obj) :=
  (I.pow 1).toModule.val.map (chartTopMapInv U).op
    (((@Modules.restrictIsoPullback S (ofOver U.obj.left) X
      (I.pow 1).toModule U.obj.hom U.obj.prop).inv.val.app
      (op (Modules.RestrictToScheme.siteObject U.obj.left ⊤))).hom
      (Modules.RestrictToScheme.sectionEquiv U.obj.left
        ((Modules.pullback U.obj.hom).obj (I.pow 1).toModule) ⊤ s))

/-- Inclusion into functions remembers the coefficient of the original ideal section. -/
def chartCoefficient (U : affineEtaleSite X)
    (s : Γ(chartIdealModule (I := I) U, ⊤)) : Γ(U.obj.left.left, ⊤) :=
  ((I.pow 1).arrow.val.app (op U.obj)).hom (chartIdealSection U s)

/-- The displayed degree-one coefficient lies in the original section ideal. -/
theorem chartCoefficient_mem (U : affineEtaleSite X)
    (s : Γ(chartIdealModule (I := I) U, ⊤)) :
    chartCoefficient U s ∈ correspondingIdeal I U :=
  sorry

/-- The actual nth ideal-power module restricted to the affine chart. -/
abbrev chartPowerModule (U : affineEtaleSite X) (n : ℕ) : U.obj.left.left.Modules :=
  (Modules.restrictToScheme U.obj.left).obj ((Modules.pullback U.obj.hom).obj (I.pow n).toModule)

/-- Read the restricted power section back at the given affine-etale object. -/
def chartPowerSection (U : affineEtaleSite X) (n : ℕ)
    (s : Γ(chartPowerModule (I := I) U n, ⊤)) :
    (I.pow n).toModule.val.obj (op U.obj) :=
  (I.pow n).toModule.val.map (chartTopMapInv U).op
    (((@Modules.restrictIsoPullback S (ofOver U.obj.left) X
      (I.pow n).toModule U.obj.hom U.obj.prop).inv.val.app
      (op (Modules.RestrictToScheme.siteObject U.obj.left ⊤))).hom
      (Modules.RestrictToScheme.sectionEquiv U.obj.left
        ((Modules.pullback U.obj.hom).obj (I.pow n).toModule) ⊤ s))

/-- The coefficient of a power section is its image under the original ideal inclusion. -/
def chartPowerCoefficient (U : affineEtaleSite X) (n : ℕ)
    (s : Γ(chartPowerModule (I := I) U n, ⊤)) : Γ(U.obj.left.left, ⊤) :=
  ((I.pow n).arrow.val.app (op U.obj)).hom (chartPowerSection U n s)

/-- On an affine chart a quasi-coherent ideal-power section has coefficient in I_A^n. -/
theorem chartPowerCoefficient_mem (U : affineEtaleSite X) (n : ℕ)
    (s : Γ(chartPowerModule (I := I) U n, ⊤)) :
    chartPowerCoefficient U n s ∈ correspondingIdeal I U ^ n := sorry

/-- The fixed coefficient map, with the actual ideal inclusion as its underlying function. -/
def chartPowerCoefficientHom (U : affineEtaleSite X) (n : ℕ) :
    Γ(chartPowerModule (I := I) U n, ⊤) →+ ↥(correspondingIdeal I U ^ n) where
  toFun s := ⟨chartPowerCoefficient U n s, chartPowerCoefficient_mem U n s⟩
  map_zero' := sorry
  map_add' := sorry

/-- Affine quasi-coherence identifies the fixed coefficient map with I_A^n.
This inverts only the given module inclusion onto its specified coefficient image. -/
theorem chartPowerCoefficientHom_bijective (U : affineEtaleSite X) (n : ℕ) :
    Function.Bijective (chartPowerCoefficientHom (I := I) U n) := sorry

/-- The section with a specified ideal-power coefficient. -/
def sectionOfPowerCoefficient (U : affineEtaleSite X) (n : ℕ)
    (a : ↥(correspondingIdeal I U ^ n)) : Γ(chartPowerModule (I := I) U n, ⊤) :=
  (Equiv.ofBijective (chartPowerCoefficientHom U n)
    (chartPowerCoefficientHom_bijective U n)).symm a

/-- Pull back the actual nth twist to the given test scheme. -/
abbrev testTwist (π : Blowup X I) {T : Over S} (x : ofOver T ⟶ π.space) (n : ℕ) :
    T.left.Modules :=
  (Modules.restrictToScheme T).obj ((Modules.pullback x).obj (π.reesTwist.twistModule n))

/-- The actual homogeneous canonical map after pullback, with only base-triangle transport. -/
def testHomogeneousMap (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (q : T ⟶ U.obj.left) (x : ofOver T ⟶ π.space)
    (w : ofOverMap q ≫ U.obj.hom = x ≫ π.hom) (n : ℕ) :
    (Scheme.Modules.pullback q.left).obj (chartPowerModule (I := I) U n) ⟶ testTwist π x n :=
  Modules.RestrictToScheme.compositePullbackComparison U.obj.hom q (I.pow n).toModule ≫
    (Modules.restrictToScheme T).map
      (eqToHom (congrArg (fun a ↦ (Modules.pullback a).obj (I.pow n).toModule) w) ≫
        (Modules.pullbackCompIso x π.hom).inv.app (I.pow n).toModule ≫
          (Modules.pullback x).map (π.reesTwist.canonicalHom n))

/-- The homogeneous section with coefficient a is obtained from the given canonical map. -/
def testHomogeneousSection (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (q : T ⟶ U.obj.left) (x : ofOver T ⟶ π.space)
    (w : ofOverMap q ≫ U.obj.hom = x ≫ π.hom) (n : ℕ)
    (a : ↥(correspondingIdeal I U ^ n)) : Γ(testTwist π x n, ⊤) :=
  (Scheme.Modules.globalSectionsMap (testHomogeneousMap π U q x w n)).hom
    ((Scheme.Modules.globalSectionsPullback q.left (chartPowerModule (I := I) U n)).hom
      (sectionOfPowerCoefficient U n a))

/-- The canonical degree-one quotient on a Rees presentation has invertible target. -/
theorem testTwist_invertible (π : Blowup X I) {T : Over S}
    (x : ofOver T ⟶ π.space) (n : ℕ) : Scheme.Modules.Invertible (testTwist π x n) :=
  sorry

/-- The actual section corresponding to a in I_A. -/
def testGeneratorSection (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (q : T ⟶ U.obj.left) (x : ofOver T ⟶ π.space)
    (w : ofOverMap q ≫ U.obj.hom = x ≫ π.hom) (a : correspondingIdeal I U) :
    Γ(testTwist π x 1, ⊤) :=
  testHomogeneousSection π U q x w 1 ⟨a.1, by simpa using a.2⟩

/-- The open where the actual image of a generates O(1). -/
def generatorOpen (π : Blowup X I) (U : affineEtaleSite X) {T : Over S}
    (q : T ⟶ U.obj.left) (x : ofOver T ⟶ π.space)
    (w : ofOverMap q ≫ U.obj.hom = x ≫ π.hom) (a : correspondingIdeal I U) : T.left.Opens :=
  (testTwist_invertible π x 1).sectionNonvanishingOpen (testGeneratorSection π U q x w a)

end AlgebraicGeometry.AlgebraicSpace.Blowup
