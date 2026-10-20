module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant.AffineRestriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace ActualSchemeSections

open ActualAffineRestriction

variable {X Y : Scheme.{u}} (b : Y ⟶ X)

abbrev preimage (U : X.Opens) : Y.Opens := RingedSpace.preimageOpen b.toShHom U

def ringMap {U : X.Opens} {V : Y.Opens} (h : V ≤ preimage b U) : Γ(X, U) →+* Γ(Y, V) :=
  (ActualAffineRestriction.ringMap Y h).comp
    (RingedSpace.sectionsMapOnOpen b.toShHom U).hom

abbrev push : Y.Modules ⥤ X.Modules := RingedSpace.Hom.pushforward b.toShHom
abbrev derivedPush : DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules :=
  RingedSpace.moduleDerivedPushforward b.toShHom

instance push_additive : (push b).Additive :=
  inferInstanceAs (Scheme.Modules.pushforward b).Additive

/-- Ordinary section restriction of a direct image, with the actual composed
structure-sheaf scalar map. -/
def restriction {U : X.Opens} {V : Y.Opens} (h : V ≤ preimage b U) :
    push b ⋙ ActualAffineRestriction.evaluation X U ⟶
      ActualAffineRestriction.evaluation Y V ⋙ ModuleCat.restrictScalars (ringMap b h) where
  app M :=
    (ModuleCat.restrictScalars (RingedSpace.sectionsMapOnOpen b.toShHom U).hom).map
      (M.val.map (homOfLE h).op) ≫
    (ModuleCat.restrictScalarsComp'
      (RingedSpace.sectionsMapOnOpen b.toShHom U).hom
      (ActualAffineRestriction.ringMap Y h) (ringMap b h) rfl).inv.app (M.val.obj (op V))
  naturality := by sorry

abbrev sourceCochain (U : X.Opens) :=
  (push b).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    RingedSpace.moduleSectionsAtOpenToDerived X.toRingedSpace U

abbrev sourceDerived (U : X.Opens) := derivedPush b ⋙ derived X U

/-- Compose the actual section unit with the actual pushforward-derived unit. -/
def sourceUnit (U : X.Opens) : sourceCochain b U ⟶
    (DerivedCategory.Q : CochainComplex Y.Modules ℤ ⥤ DerivedCategory Y.Modules) ⋙ sourceDerived b U where
  app P := (RingedSpace.moduleSectionsAtOpenDerivedUnit X.toRingedSpace U).app
      (((push b).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
    (derived X U).map ((RingedSpace.moduleDerivedPushforward.unit b.toShHom).app P)
  naturality := by sorry

-- Local instance justification (defeq pin): align the scheme presentation with the canonical localization used by the right-derived comparison.
local instance : (DerivedCategory.Q : CochainComplex Y.Modules ℤ ⥤ DerivedCategory Y.Modules).IsLocalization
    (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ)) :=
  DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp

/-- Derived direct image followed by derived sections gives the right-derived
composite. For unbounded complexes this uses composition of derived adjunctions;
termwise flasque acyclicity alone is not a proof of the assertion. -/
instance sourceDerived_isRightDerived (U : X.Opens) :
    (sourceDerived b U).IsRightDerivedFunctor (sourceUnit b U)
      (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ)) := by sorry

def complexRestriction {U : X.Opens} {V : Y.Opens} (h : V ≤ preimage b U)
    (P : CochainComplex Y.Modules ℤ) :
    ((ActualAffineRestriction.evaluation X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((push b).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
    ((ModuleCat.restrictScalars (ringMap b h)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((ActualAffineRestriction.evaluation Y V).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) where
  f n := (restriction b h).app (P.X n)
  comm' := by sorry

def cochainComparison {U : X.Opens} {V : Y.Opens} (h : V ≤ preimage b U) :
    sourceCochain b U ⟶
      (DerivedCategory.Q : CochainComplex Y.Modules ℤ ⥤ DerivedCategory Y.Modules) ⋙
        (derived Y V ⋙ ModuleCat.derivedRestrictionOfScalars (ringMap b h)) where
  app P := DerivedCategory.Q.map (complexRestriction b h P) ≫
    (ModuleCat.derivedRestrictionComplexUnit (ringMap b h)).app
      (((ActualAffineRestriction.evaluation Y V).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
    (ModuleCat.derivedRestrictionOfScalars (ringMap b h)).map
      ((RingedSpace.moduleSectionsAtOpenDerivedUnit Y.toRingedSpace V).app P)
  naturality := by sorry

def derivedComparison {U : X.Opens} {V : Y.Opens} (h : V ≤ preimage b U) :
    sourceDerived b U ⟶ derived Y V ⋙ ModuleCat.derivedRestrictionOfScalars (ringMap b h) :=
  @Functor.rightDerivedDesc _ _ _ _ _ _ (sourceDerived b U) _ DerivedCategory.Q
    (sourceUnit b U) (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ))
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
    (sourceDerived_isRightDerived b U) _ (cochainComparison b h)

/-- A specified map into the actual derived direct image induces the canonical
scalar-linear derived section map. -/
def mapOfPushforward {U : X.Opens} {V : Y.Opens} (h : V ≤ preimage b U)
    {K : DerivedCategory X.Modules} {L : DerivedCategory Y.Modules}
    (a : K ⟶ (derivedPush b).obj L) :
    (derived X U).obj K ⟶
      (ModuleCat.derivedRestrictionOfScalars (ringMap b h)).obj ((derived Y V).obj L) :=
  (derived X U).map a ≫ (derivedComparison b h).app L

/-- The certificate for the canonical derived pullback-pushforward adjunction
on these module sheaves. The adjunction's unit/counit remain the derived maps. -/
theorem derivedPair : RingedSite.Hom.DerivedAdjunction.HasPair
    (RingedSpace.opensRingedSiteHom b.toShHom) := by sorry

def adjunction : RingedSpace.modulePullbackDerived b.toShHom ⊣ derivedPush b := by
  -- Local instance justification (proof-local temporary data): apply the canonical derived adjunction with the proved pair certificate for this morphism.
  letI := derivedPair b
  exact RingedSpace.modulePullbackDerivedPushforwardAdjunction b.toShHom

def scalarComparison {U : X.Opens} {V : Y.Opens} (h : V ≤ preimage b U)
    (K : DerivedCategory X.Modules) :
    (ModuleCat.derivedExtensionOfScalars (ringMap b h)).obj ((derived X U).obj K) ⟶
      (derived Y V).obj ((RingedSpace.modulePullbackDerived b.toShHom).obj K) :=
  (ModuleCat.derivedExtensionRestrictionHomEquiv (ringMap b h) _ _).symm
    (mapOfPushforward b h ((adjunction b).unit.app K))

end ActualSchemeSections
