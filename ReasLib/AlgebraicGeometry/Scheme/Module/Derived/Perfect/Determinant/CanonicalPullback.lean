module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant.Functor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Sections.AffineBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Basis.SectionFamilies

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace ActualDeterminantPullback

open ActualAffineRestriction ActualGlobalDeterminant

variable {X Y : Scheme.{u}} (b : Y ⟶ X) (K : Perfect X)

abbrev pulledObject : Perfect Y := (Scheme.PerfectDerived.TorNegOneZero.pullback b).obj K

instance affineScalarComparison_isIso (U : X.affineOpens) (V : Y.affineOpens)
    (h : V.1 ≤ ActualSchemeSections.preimage b U.1) :
    IsIso (ActualSchemeSections.scalarComparison b h K.obj.obj) := by sorry

/-- The affine derived comparison is the actual scalar transpose, on affine
charts, of the derived pullback unit. -/
def affineObjectIso (U : X.affineOpens) (V : Y.affineOpens)
    (h : V.1 ≤ ActualSchemeSections.preimage b U.1) :
    CanonicalRingDeterminant.extendedObject (ActualSchemeSections.ringMap b h)
        (affineObject X K U) ≅ affineObject Y (pulledObject b K) V :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (@asIso _ _ _ _ (ActualSchemeSections.scalarComparison b h K.obj.obj)
      (affineScalarComparison_isIso b K U V h)))

def affineLineIso (U : X.affineOpens) (V : Y.affineOpens)
    (h : V.1 ≤ ActualSchemeSections.preimage b U.1) :
    (ModuleCat.extendScalars (ActualSchemeSections.ringMap b h)).obj (line X K U) ≅
      line Y (pulledObject b K) V :=
  CanonicalRingDeterminant.baseChangeIso (ActualSchemeSections.ringMap b h) (affineObject X K U) ≪≫
    (ObjectProperty.ι _).mapIso
      ((CanonicalRingDeterminant.determinantFunctor Γ(Y, V.1)).map
        ⟨affineObjectIso b K U V h⟩).iso

def affineRestriction (U : X.affineOpens) (V : Y.affineOpens)
    (h : V.1 ≤ ActualSchemeSections.preimage b U.1) :
    line X K U ⟶ (ModuleCat.restrictScalars (ActualSchemeSections.ringMap b h)).obj
      (line Y (pulledObject b K) V) :=
  (ModuleCat.extendRestrictScalarsAdj (ActualSchemeSections.ringMap b h)).homEquiv _ _
    (affineLineIso b K U V h).hom

def affineOfBasis (Z : Scheme.{u}) (U : BasisOpen Z.affineOpens) : Z.affineOpens :=
  ⟨U.obj, U.property⟩

/-- Map affine sections using the actual projection comparisons, the scalar
transpose above, and the inverse projection on the target affine. -/
def basisMap (V : BasisOpen Y.affineOpens) (U : BasisOpen X.affineOpens)
    (h : V.obj ≤ (Opens.map b.base).obj U.obj) :
    (lineSheaf X K).val.presheaf.obj (op U.obj) ⟶
      (lineSheaf Y (pulledObject b K)).val.presheaf.obj (op V.obj) :=
  AddCommGrpCat.ofHom
    { toFun := fun s ↦
        (affineSectionsIso Y (pulledObject b K) (affineOfBasis Y V)).inv
          ((affineRestriction b K (affineOfBasis X U) (affineOfBasis Y V) h).hom
            ((affineSectionsIso X K (affineOfBasis X U)).hom s))
      map_zero' := by sorry
      map_add' := by sorry }

def basisFamily : TopCat.Presheaf.BasisPushforwardHomFamily b.base Y.affineOpens X.affineOpens
    (lineSheaf X K).val.presheaf (lineSheaf Y (pulledObject b K)).val.presheaf where
  app V U h := basisMap b K V U h
  source_naturality := by sorry
  target_naturality := by sorry

def linearFamily : RingedSpace.Module.BasisPushforwardHomFamily.LinearFamily
    (BX := Y.affineOpens) (BY := X.affineOpens)
    (ℱ := lineSheaf Y (pulledObject b K)) (𝒢 := lineSheaf X K) b.toShHom :=
  ⟨basisFamily b K, by sorry⟩

/-- Unique extension of the SPECIFIED affine section maps. This is the basis
extension universal property, not a bare chosen sheaf isomorphism. -/
def pushforwardMap : lineSheaf X K ⟶
    (Scheme.Modules.pushforward b).obj (lineSheaf Y (pulledObject b K)) :=
  RingedSpace.Module.BasisPushforwardHomFamily.toHom b.toShHom
    Y.isBasis_affineOpens X.isBasis_affineOpens (linearFamily b K)

/-- The determinant pullback map is the actual sheaf-module adjoint transpose. -/
def pullbackMap : (Scheme.Modules.pullback b).obj (lineSheaf X K) ⟶
    lineSheaf Y (pulledObject b K) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _).symm (pushforwardMap b K)

instance pullbackMap_isIso : IsIso (pullbackMap b K) := by sorry

def pullbackIso : (Scheme.Modules.pullback b).obj (lineSheaf X K) ≅
    lineSheaf Y (pulledObject b K) := asIso (pullbackMap b K)

theorem pulledRankZero (hK : isRankZero X K) : isRankZero Y (pulledObject b K) := by sorry

theorem pullbackIso_delta (hK : isRankZero X K) :
    SheafOfModules.sectionsMap (pullbackIso b K).hom
      (RingedSpace.Hom.pullbackSections b.toShHom (delta X K hK)) =
      delta Y (pulledObject b K) (pulledRankZero b K hK) := by sorry

end ActualDeterminantPullback
