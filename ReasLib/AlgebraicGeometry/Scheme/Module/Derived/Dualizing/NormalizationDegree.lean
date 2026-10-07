module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Stalk
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex

/-- A function records the normalization degrees of the derived stalks of a dualizing complex when its value at each point gives the shift of the residue field obtained by derived coextension. -/
def IsStalkNormalizationDegreeFunction
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (ω : RingedSpace.ModuleDerived X.toRingedSpace) (δ : X → ℤ) : Prop :=
  ∀ x : X,
    Nonempty
      ((ModuleCat.derivedCoextensionOfScalars
          (algebraMap (X.presheaf.stalk x)
            (IsLocalRing.ResidueField (X.presheaf.stalk x)))).obj
          (RingedSpace.ModuleDerived.Stalk.obj ω x) ≅
        (shiftFunctor
          (DerivedCategory
            (ModuleCat.{u} (IsLocalRing.ResidueField (X.presheaf.stalk x)))) (δ x)).obj
          (ModuleCat.single0
            (ModuleCat.of (IsLocalRing.ResidueField (X.presheaf.stalk x))
              (IsLocalRing.ResidueField (X.presheaf.stalk x)))))

/-- The residue-field characterization of a stalk normalization degree at a point. -/
theorem IsStalkNormalizationDegreeFunction.at
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} {δ : X → ℤ}
    (hδ : IsStalkNormalizationDegreeFunction ω δ) (x : X) :
    Nonempty
      ((ModuleCat.derivedCoextensionOfScalars
          (algebraMap (X.presheaf.stalk x)
            (IsLocalRing.ResidueField (X.presheaf.stalk x)))).obj
          (RingedSpace.ModuleDerived.Stalk.obj ω x) ≅
        (shiftFunctor
          (DerivedCategory
            (ModuleCat.{u} (IsLocalRing.ResidueField (X.presheaf.stalk x)))) (δ x)).obj
          (ModuleCat.single0
            (ModuleCat.of (IsLocalRing.ResidueField (X.presheaf.stalk x))
              (IsLocalRing.ResidueField (X.presheaf.stalk x))))) := sorry

/-- The canonical normalization-degree function determined by a dualizing complex on a locally Noetherian scheme. -/
noncomputable def normalizationDegree
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : Scheme.IsDualizingComplex ω) : X → ℤ :=
  @dite (X → ℤ) (∃ δ : X → ℤ, IsStalkNormalizationDegreeFunction ω δ)
    (Classical.propDecidable _) (fun h ↦ Classical.choose h) (fun _ _ ↦ 0)

/-- The canonical normalization-degree function has the defining stalkwise property. -/
theorem normalizationDegree_spec
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : Scheme.IsDualizingComplex ω) :
    IsStalkNormalizationDegreeFunction ω (normalizationDegree hω) := sorry

/-- Any stalk normalization-degree function of a fixed dualizing complex is the canonical one. -/
theorem normalizationDegree_eq
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : Scheme.IsDualizingComplex ω)
    {δ : X → ℤ} (hδ : IsStalkNormalizationDegreeFunction ω δ) : δ = normalizationDegree hω := sorry

/-- Shifting a derived stalk by the negative canonical normalization degree gives a normalized dualizing complex over the local ring at that point. -/
theorem normalizationDegree_stalkShift_isNormalized
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {ω : RingedSpace.ModuleDerived X.toRingedSpace} (hω : Scheme.IsDualizingComplex ω)
    [monoidal : ∀ x : X, MonoidalCategory (DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x)))]
    (H : ∀ x : X, @MonoidalClosed _ inferInstance (monoidal x)) (x : X) :
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x)))
      (-(normalizationDegree hω x))).obj (RingedSpace.ModuleDerived.Stalk.obj ω x)).IsNormalizedDualizingComplex (H x) := sorry

end AlgebraicGeometry.Scheme.IsDualizingComplex
