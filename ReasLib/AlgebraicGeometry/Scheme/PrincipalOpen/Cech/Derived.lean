module

public import ReasLib.AlgebraicGeometry.Scheme.PrincipalOpen.Cech.Alternating
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal

/-!
# Derived comparison for principal-open alternating Cech complexes

For a finite principal-open family on an affine scheme, this module compares the total strict
alternating Cech construction on termwise quasi-coherent complexes with derived sections on the
covered open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape RingedSpace.Module.Derived.Sections

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PrincipalOpenCech

variable {A : Type u} [CommRing A] {r : ℕ}

/-- Complexes of modules on `Spec(A)` whose terms are quasi-coherent. -/
abbrev QuasiCoherentComplex (A : Type u) [CommRing A] :=
  CochainComplex.TermsIn ℤ
    (RingedSpace.quasiCoherentModuleProperty (Spec (CommRingCat.of A)).toRingedSpace)

/-- Quasi-isomorphisms of termwise quasi-coherent complexes, detected on the underlying
complexes of module sheaves. -/
abbrev quasiCoherentQuasiIso (A : Type u) [CommRing A] :
    MorphismProperty (QuasiCoherentComplex A) :=
  (HomologicalComplex.quasiIso
    (Spec (CommRingCat.of A)).toRingedSpace.Modules (up ℤ)).inverseImage
      CochainComplex.TermsIn.ι

/-- The total strictly indexed principal-open alternating Cech source, restricted to termwise
quasi-coherent complexes. -/
abbrev quasiCoherentSource (f : Fin r → A) :
    QuasiCoherentComplex A ⥤ DerivedCategory (ModuleCat.{u, u} A) :=
  CochainComplex.TermsIn.ι ⋙ Alternating.source f

/-- Evaluating the quasi-coherent alternating Cech source forgets to the underlying complex
before applying the strict source functor. -/
theorem quasiCoherentSource_obj (f : Fin r → A)
    (K : CochainComplex.TermsIn ℤ
      (RingedSpace.quasiCoherentModuleProperty (Spec (CommRingCat.of A)).toRingedSpace)) :
    (quasiCoherentSource f).obj K = (Alternating.source f).obj K.obj := sorry

/-- Derived sections on `openSubset f`, transported along
`A ≅ Γ(Spec(A), O)` and viewed as an object of `D(A)`. -/
abbrev target (f : Fin r → A) :
    CochainComplex (Spec (CommRingCat.of A)).toRingedSpace.Modules ℤ ⥤
      DerivedCategory (ModuleCat.{u, u} A) :=
  DerivedCategory.Q ⋙
    OverGlobal.derived (Spec (CommRingCat.of A)).toRingedSpace (openSubset f) ⋙
    ModuleCat.derivedRestrictionOfScalars (ΓSpecIso (CommRingCat.of A)).inv.hom

/-- Derived sections on `openSubset f`, restricted to termwise quasi-coherent complexes. -/
abbrev quasiCoherentTarget (f : Fin r → A) :
    QuasiCoherentComplex A ⥤ DerivedCategory (ModuleCat.{u, u} A) :=
  CochainComplex.TermsIn.ι ⋙ target f

/-- Sections on `openSubset f`, restricted to termwise quasi-coherent complexes and viewed
in `D(A)`. -/
abbrev quasiCoherentSections (f : Fin r → A) :
    QuasiCoherentComplex A ⥤ DerivedCategory (ModuleCat.{u, u} A) :=
  CochainComplex.TermsIn.ι ⋙
    (Alternating.sectionsOnUnion f).mapHomologicalComplex (up ℤ) ⋙
    DerivedCategory.Q ⋙
    ModuleCat.derivedRestrictionOfScalars (ΓSpecIso (CommRingCat.of A)).inv.hom

/-- The canonical augmentation from sections on the principal-open union to the strict
alternating Cech totalization, restricted to termwise quasi-coherent complexes. -/
noncomputable def quasiCoherentAugmentation (f : Fin r → A) :
    quasiCoherentSections f ⟶ quasiCoherentSource f :=
  Functor.whiskerRight
    (Functor.whiskerLeft CochainComplex.TermsIn.ι
      (Alternating.augmentationNatTrans f))
    (DerivedCategory.Q ⋙
      ModuleCat.derivedRestrictionOfScalars (ΓSpecIso (CommRingCat.of A)).inv.hom)

/-- The canonical derived-sections unit on termwise quasi-coherent complexes. -/
noncomputable def quasiCoherentUnit (f : Fin r → A) :
    quasiCoherentSections f ⟶ quasiCoherentTarget f :=
  Functor.whiskerLeft CochainComplex.TermsIn.ι
    (Functor.whiskerRight
      (OverGlobal.unit (Spec (CommRingCat.of A)).toRingedSpace (openSubset f))
      (ModuleCat.derivedRestrictionOfScalars (ΓSpecIso (CommRingCat.of A)).inv.hom))

/-- The strict alternating Cech source sends quasi-isomorphisms between termwise
quasi-coherent complexes to isomorphisms in `D(A)`. -/
theorem quasiCoherentSource_inverts (f : Fin r → A) :
    (quasiCoherentQuasiIso A).IsInvertedBy (quasiCoherentSource f) := sorry

/-- Derived sections on the principal-open union send quasi-isomorphisms between termwise
quasi-coherent complexes to isomorphisms in `D(A)`. -/
theorem quasiCoherentTarget_inverts (f : Fin r → A) :
    (quasiCoherentQuasiIso A).IsInvertedBy (quasiCoherentTarget f) := sorry

/-- The strict alternating Cech source descended to the localization of termwise
quasi-coherent complexes at quasi-isomorphisms. -/
noncomputable def derivedSource (f : Fin r → A) :
    (quasiCoherentQuasiIso A).Localization ⥤
      DerivedCategory (ModuleCat.{u, u} A) :=
  Localization.lift (quasiCoherentSource f) (quasiCoherentSource_inverts f)
    (quasiCoherentQuasiIso A).Q

/-- Derived sections descended to the localization of termwise quasi-coherent complexes at
quasi-isomorphisms. -/
noncomputable def derivedTarget (f : Fin r → A) :
    (quasiCoherentQuasiIso A).Localization ⥤
      DerivedCategory (ModuleCat.{u, u} A) :=
  Localization.lift (quasiCoherentTarget f) (quasiCoherentTarget_inverts f)
    (quasiCoherentQuasiIso A).Q

/-- The canonical factorization isomorphism from the localized strict Cech source to its
original functor on termwise quasi-coherent complexes. -/
noncomputable def derivedSourceFac (f : Fin r → A) :
    (quasiCoherentQuasiIso A).Q ⋙ derivedSource f ≅ quasiCoherentSource f :=
  Localization.fac (quasiCoherentSource f) (quasiCoherentSource_inverts f)
    (quasiCoherentQuasiIso A).Q

/-- The canonical factorization isomorphism from localized derived sections to the original
functor on termwise quasi-coherent complexes. -/
noncomputable def derivedTargetFac (f : Fin r → A) :
    (quasiCoherentQuasiIso A).Q ⋙ derivedTarget f ≅ quasiCoherentTarget f :=
  Localization.fac (quasiCoherentTarget f) (quasiCoherentTarget_inverts f)
    (quasiCoherentQuasiIso A).Q

/-- The Cech augmentation regarded as the unit of the localized strict Cech model. -/
noncomputable def derivedSourceUnit (f : Fin r → A) :
    quasiCoherentSections f ⟶ (quasiCoherentQuasiIso A).Q ⋙ derivedSource f :=
  quasiCoherentAugmentation f ≫ (derivedSourceFac f).inv

/-- The derived-sections unit transported to the localization of termwise quasi-coherent
complexes. -/
noncomputable def derivedTargetUnit (f : Fin r → A) :
    quasiCoherentSections f ⟶ (quasiCoherentQuasiIso A).Q ⋙ derivedTarget f :=
  quasiCoherentUnit f ≫ (derivedTargetFac f).inv

/-- The localized strict alternating Cech construction is a right-derived model of sections
on the principal-open union. -/
noncomputable instance derivedSource_isRightDerived (f : Fin r → A) :
    (derivedSource f).IsRightDerivedFunctor
      (derivedSourceUnit f) (quasiCoherentQuasiIso A) := sorry

/-- Evaluating the quasi-coherent target forgets to the underlying complex before taking derived
sections. -/
theorem quasiCoherentTarget_obj (f : Fin r → A)
    (K : CochainComplex.TermsIn ℤ
      (RingedSpace.quasiCoherentModuleProperty (Spec (CommRingCat.of A)).toRingedSpace)) :
    (quasiCoherentTarget f).obj K = (target f).obj K.obj := sorry

/-- A natural transformation from the strict alternating Cech totalization to derived sections
is compatible with the canonical comparison when it carries the union-sections augmentation to
the derived-sections unit. -/
def IsComparison (f : Fin r → A)
    (comparison : quasiCoherentSource f ⟶ quasiCoherentTarget f) : Prop :=
  ∀ K : CochainComplex.TermsIn ℤ
      (RingedSpace.quasiCoherentModuleProperty (Spec (CommRingCat.of A)).toRingedSpace),
    let X := (Spec (CommRingCat.of A)).toRingedSpace
    let scalarRestriction := ModuleCat.derivedRestrictionOfScalars
      (ΓSpecIso (CommRingCat.of A)).inv.hom
    scalarRestriction.map
        (DerivedCategory.Q.map
          ((Alternating.augmentationNatTrans f).app K.obj)) ≫
        comparison.app K =
      scalarRestriction.map
        ((OverGlobal.unit X (openSubset f)).app K.obj)

/-- The comparison between the localized Cech and derived-sections models induced by their
canonical units. -/
noncomputable def derivedComparisonHom (f : Fin r → A) :
    derivedSource f ⟶ derivedTarget f :=
  (derivedSource f).rightDerivedDesc
    (derivedSourceUnit f) (quasiCoherentQuasiIso A)
    (derivedTarget f) (derivedTargetUnit f)

/-- The canonical functorial comparison from the strict alternating Cech totalization to
derived sections on the principal-open union. -/
noncomputable def comparisonHom (f : Fin r → A) :
    quasiCoherentSource f ⟶ quasiCoherentTarget f :=
  (derivedSourceFac f).inv ≫
    Functor.whiskerLeft (quasiCoherentQuasiIso A).Q (derivedComparisonHom f) ≫
    (derivedTargetFac f).hom

/-- The canonical comparison factors the derived-sections unit through the strict alternating
Cech augmentation. -/
theorem comparisonHom_isComparison (f : Fin r → A) :
    IsComparison f (comparisonHom f) := sorry

/-- For the union `U = ⨆ i, D(f i) ⊆ Spec(A)`, every component of the canonical
functorial comparison from the total strictly indexed alternating Cech complex of a termwise
quasi-coherent complex to `RΓ(U, -)` is an isomorphism in `D(A)`. -/
instance comparison_isIso (f : Fin r → A) (K : QuasiCoherentComplex A) :
    IsIso ((comparisonHom f).app K) := sorry

end AlgebraicGeometry.Scheme.PrincipalOpenCech
