module

public import ReasLib.AlgebraicGeometry.Surface.CubicQuartic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Modification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PuncturedSpectrum
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.CubicQuarticSurface

/-- The algebraic space `specSpace localRing` is integral. -/
instance instIsIntegral_specSpace_localRing :
    AlgebraicSpace.IsIntegral (AlgebraicSpace.specSpace localRing) := sorry

end AlgebraicGeometry.CubicQuarticSurface

namespace AlgebraicGeometry.AlgebraicSpace

/-- There exists an excellent 2-dimensional Noetherian local ring whose spectrum
admits an integral algebraic-space modification that is not a scheme. -/
@[stacks 0AEB]
theorem exists_modification_not_scheme :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A) (_ : IsLocalRing A)
      (_ : IsExcellentRing A),
      ringKrullDim A = 2 ∧
        ∃ (X : AlgebraicSpace (Spec (.of A))) (f : X ⟶ specSpace A)
          (_ : IsIntegral X) (_ : IsIntegral (specSpace A)),
          IsModification f ∧ ¬ IsScheme X := sorry

/-- The cubic-quartic surface local ring admits an integral algebraic-space
modification of its spectrum that is not a scheme. -/
theorem exists_modification_not_scheme_localRing :
    ∃ (X : AlgebraicSpace (Spec (.of CubicQuarticSurface.localRing)))
      (f : X ⟶ specSpace CubicQuarticSurface.localRing)
      (_ : IsIntegral X) (_ : IsIntegral (specSpace CubicQuarticSurface.localRing)),
      IsModification f ∧ ¬ IsScheme X := sorry

end AlgebraicGeometry.AlgebraicSpace
