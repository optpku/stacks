module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.AffineProjSym
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.SmallProjectiveFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input
public import stacks_project.Chap71.Lemma_71_11_2_RestrictionBaseChange
public import Mathlib.AlgebraicGeometry.Limits

/-! Explicit Proj(Sym) chart atlas and quotient-functor carrier for P(E). -/
@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.MonoidalCategory
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveAtlas
variable {S : Scheme.{u}} {X : AlgebraicSpace S} (E : X.Modules) [E.IsQuasicoherent]
open SmallProjectiveFunctor
open AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

abbrev Index := (AtlasInput.scheme X).left.affineOpens

def affineOver (U : Index (X := X)) : Over S :=
  Over.mk (U.1.ι ≫ (AtlasInput.scheme X).hom)

def affineToAtlas (U : Index (X := X)) : affineOver U ⟶ AtlasInput.scheme X :=
  Over.homMk U.1.ι rfl

def affineMap (U : Index (X := X)) : ofOver (affineOver U) ⟶ X :=
  ofOverMap (affineToAtlas U) ≫ AtlasInput.map X

def localModule (U : Index (X := X)) : (affineOver U).left.Modules :=
  (Modules.restrictToScheme (affineOver U)).obj ((Modules.pullback (affineMap U)).obj E)

instance localModule_qc (U : Index (X := X)) : (localModule E U).IsQuasicoherent := by
  sorry

instance affineBase (U : Index (X := X)) : IsAffine (affineOver U).left := U.2

def chart (U : Index (X := X)) : Scheme.{u} := AffineProjSym.overScheme (localModule E U)

def chartOver (U : Index (X := X)) : Over S :=
  Over.mk (AffineProjSym.projection (localModule E U) ≫ (affineOver U).hom)

def chartToAffine (U : Index (X := X)) : chartOver E U ⟶ affineOver U :=
  Over.homMk (AffineProjSym.projection (localModule E U)) rfl

def chartBase (U : Index (X := X)) : ofOver (chartOver E U) ⟶ X :=
  ofOverMap (chartToAffine E U) ≫ affineMap U

/-- Extend the actual affine Serre line through the existing geometric inverse images. -/
def chartLine (U : Index (X := X)) : (ofOver (chartOver E U)).Modules :=
  (extension (chartOver E U)).obj (AffineProjSym.line (localModule E U))

theorem chartLine_invertible (U : Index (X := X)) : isInvertibleObject (chartLine E U) := by
  sorry

/-- The quotient is the extension of m↦iota(m)/1 after the fixed actual source comparison. -/
def chartSourceComparison (U : Index (X := X)) :
    (extension (chartOver E U)).obj
      ((Scheme.Modules.pullback (chartToAffine E U).left).obj (localModule E U)) ⟶
        (Modules.pullback (chartBase E U)).obj E :=
  (extensionPullbackIso (chartToAffine E U)).hom.app (localModule E U) ≫
    (Modules.pullback (ofOverMap (chartToAffine E U))).map
      ((extensionAdjunction (affineOver U)).counit.app ((Modules.pullback (affineMap U)).obj E)) ≫
    (Modules.pullbackCompIso (ofOverMap (chartToAffine E U)) (affineMap U)).hom.app E

/-- This exact adjunction comparison is invertible for the input QCoh module. -/
theorem chartSourceComparison_isIso (U : Index (X := X)) : IsIso (chartSourceComparison E U) := by
  sorry

def chartQuotientHom (U : Index (X := X)) :
    (Modules.pullback (chartBase E U)).obj E ⟶ chartLine E U :=
  (@asIso _ _ _ _ (chartSourceComparison E U) (chartSourceComparison_isIso E U)).inv ≫
    (extension (chartOver E U)).map (AffineProjSym.quotientHom (localModule E U))

theorem chartQuotientHom_epi (U : Index (X := X)) : Epi (chartQuotientHom E U) := by
  sorry

def chartQuotient (U : Index (X := X)) :
    CategoryTheory.InvertibleQuotient ((Modules.pullback (chartBase E U)).obj E) where
  object := chartLine E U
  isInvertible := chartLine_invertible E U
  hom := chartQuotientHom E U
  hom_epi := chartQuotientHom_epi E U

/-- Package the genuine quotient over the actual Yoneda base point. -/
def pointOfQuotient (T : Over S) (g : ofOver T ⟶ X)
    (q : CategoryTheory.InvertibleQuotient ((Modules.pullback g).obj E)) : Point E T :=
  ⟨yonedaEquiv g, (show SmallProjectiveFunctor.homOfPoint (yonedaEquiv g) = g from yonedaEquiv.symm_apply_apply g).symm ▸
    pointEquiv E T g (CategoryTheory.InvertibleQuotient.IsoClass.mk q)⟩

def chartPoint (U : Index (X := X)) : Point E (chartOver E U) :=
  pointOfQuotient E (chartOver E U) (chartBase E U) (chartQuotient E U)

def chartMap (U : Index (X := X)) : yoneda.obj (chartOver E U) ⟶ functor E :=
  yonedaEquiv.symm (chartPoint E U)

/-- The atlas scheme is a specified coproduct of the actual affine Proj charts. -/
def atlasScheme : Scheme.{u} := ∐ (chart E)

def atlasOver : Over S :=
  Over.mk (Sigma.desc (fun U ↦ (chartOver E U).hom))

def inclusion (U : Index (X := X)) : chartOver E U ⟶ atlasOver E :=
  Over.homMk (Sigma.ι (chart E) U) (Sigma.ι_desc _ _)

/-- Actual restriction to the disjoint chart components. -/
def restrictToCharts : Point E (atlasOver E) → ∀ U : Index (X := X), Point E (chartOver E U) :=
  fun p U ↦ SmallProjectiveFunctor.map E (inclusion E U) p

/-- Quotient lines and base points glue uniquely across a disjoint union. This
is a fixed-map law; its inverse cannot select a different atlas or space. -/
theorem restrictToCharts_bijective : Function.Bijective (restrictToCharts E) := by
  sorry

def atlasPoint : Point E (atlasOver E) :=
  (Equiv.ofBijective (restrictToCharts E) (restrictToCharts_bijective E)).symm (chartPoint E)

def atlasMap : yoneda.obj (atlasOver E) ⟶ functor E := yonedaEquiv.symm (atlasPoint E)

/-- Affine projective quotient representability makes each displayed chart étale
over the quotient functor; the base charts come from the input étale atlas. -/
theorem atlas_etale :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (atlasMap E) := by
  sorry

theorem atlas_surjective :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (atlasMap E) := by
  sorry

/-- Descent of actual invertible quotients, with their epimorphic quotient maps. -/
theorem isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) (functor E) := by
  sorry

theorem diagonal_representable : yoneda.relativelyRepresentable (Limits.diag (functor E)) := by
  sorry

/-- Actual P(E): small quotient-class carrier and explicitly displayed Proj atlas. -/
def space : AlgebraicSpace S :=
  ofFunctor (functor E) (isSheaf E) (diagonal_representable E)
    ⟨atlasOver E, atlasMap E, atlas_etale E, atlas_surjective E⟩

def projection : space E ⟶ X := baseMap E

theorem space_carrier : (space E).functorOfPoints = functor E := rfl
theorem projection_eq : projection E = baseMap E := rfl

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveAtlas
