module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Algebra.Total
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Construction
public import ReasLib.AlgebraicGeometry.Scheme.VectorBundle.Basic

/-!
# Normal cones and normal bundles

The normal cone of an immersion is the relative spectrum of its total conormal algebra. Its
normal bundle is the relative spectrum of the symmetric algebra of its conormal sheaf.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X Z : Scheme.{u}}

/-- The normal cone of an immersion, represented by an explicit relative-spectrum model of its
total conormal algebra. -/
noncomputable def normalCone (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P] :
    Scheme.{u} :=
  relativeSpec P

/-- The structural morphism from the normal cone of an immersion to its source scheme. -/
noncomputable def normalConeπ (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P] :
    normalCone i P ⟶ Z :=
  relativeSpecπ P

/-- The normal cone is the relative spectrum of the total conormal algebra. -/
theorem normalCone_eq_relativeSpec (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (ConormalAlgebra.total i)) [IsRelativeSpectrumOver P] :
    normalCone i P = relativeSpec P :=
  rfl

/-- The normal bundle of an immersion, represented by an explicit relative-spectrum model of
the symmetric algebra of its conormal sheaf. -/
noncomputable def normalBundle (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i)))
    [IsRelativeSpectrumOver P] : Scheme.{u} :=
  associatedVectorBundle (Hom.conormalSheaf i) P

/-- The structural morphism from the normal bundle of an immersion to its source scheme. -/
noncomputable def normalBundleπ (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i)))
    [IsRelativeSpectrumOver P] : normalBundle i P ⟶ Z :=
  associatedVectorBundleπ (Hom.conormalSheaf i) P

/-- The normal bundle is the relative spectrum of the symmetric algebra of the conormal sheaf. -/
theorem normalBundle_eq_relativeSpec (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i)))
    [IsRelativeSpectrumOver P] : normalBundle i P = relativeSpec P :=
  rfl

/-- The normal bundle is the vector bundle associated to the conormal sheaf. -/
theorem normalBundle_eq_associatedVectorBundle (i : Z ⟶ X) [IsImmersion i]
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i)))
    [IsRelativeSpectrumOver P] :
    normalBundle i P = associatedVectorBundle (Hom.conormalSheaf i) P :=
  rfl

end AlgebraicGeometry.Scheme
