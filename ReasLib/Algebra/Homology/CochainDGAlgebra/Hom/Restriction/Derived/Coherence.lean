/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence for derived change of scalars

Derived restriction is contravariantly functorial in a DGA homomorphism.  Its identity and
composition comparisons descend from the strict ordinary restriction functors.  The matching
comparisons for derived extension are then the canonical isomorphisms between left adjoints to
the same restriction functor.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory DifferentialGradedCategory

namespace CochainDGAlgebra.Hom

variable {R : Type u} [CommRing R]

/-- Restriction along an identity DGA map induces the identity functor on DG homotopy
categories. -/
theorem restrictMapK_id (A : CochainDGAlgebra.{u, v} R) :
    (restrictDgFunctor (𝟙 A)).mapK =
      𝟭 (K R (DifferentialGradedModule.{u, w} A)) := sorry

namespace Derived

variable {A B C : CochainDGAlgebra.{u, v} R}

/-- The source-level factorization identifying restriction along an identity with the
localization functor. -/
noncomputable def restrictionIdFactors (A : CochainDGAlgebra.{u, v} R) :
    (restrictDgFunctor (𝟙 A)).mapK ⋙
        DifferentialGradedModule.Derived.Q A ≅
      DifferentialGradedModule.Derived.Q A :=
  Functor.isoWhiskerRight (eqToIso (restrictMapK_id A))
      (DifferentialGradedModule.Derived.Q A) ≪≫
    Functor.leftUnitor (DifferentialGradedModule.Derived.Q A)

/-- Derived restriction along an identity DGA map is canonically the identity. -/
@[stacks 0BYX "identity coherence for derived restriction of scalars"]
noncomputable def restrictionIdIso (A : CochainDGAlgebra.{u, v} R) :
    𝟭 (DifferentialGradedModule.Derived.Category.{u, w} A) ≅
      restriction (𝟙 A) :=
  Localization.liftNatIso
    (DifferentialGradedModule.Derived.Q A)
    (DifferentialGradedModule.quasiIso A)
    (DifferentialGradedModule.Derived.Q A)
    ((restrictDgFunctor (𝟙 A)).mapK ⋙
      DifferentialGradedModule.Derived.Q A)
    (𝟭 (DifferentialGradedModule.Derived.Category.{u, w} A))
    (restriction (𝟙 A)) (restrictionIdFactors A).symm

/-- The canonical factorization of two successive derived restrictions through restriction
along the composite DGA map. -/
noncomputable def restrictionCompFactors (f : A ⟶ B) (g : B ⟶ C) :
    DifferentialGradedModule.Derived.Q C ⋙
        (restriction g ⋙ restriction f) ≅
      (f ≫ g).restrictDgFunctor.mapK ⋙
        DifferentialGradedModule.Derived.Q A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictionFac g) (restriction f) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft g.restrictDgFunctor.mapK (restrictionFac f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (eqToIso (CochainDGAlgebra.Hom.restrictDgFunctor_mapK_comp g f)).symm
      (DifferentialGradedModule.Derived.Q A)

/-- Successive derived restrictions form a canonical lift of ordinary restriction along the
composite DGA map. -/
noncomputable instance restrictionCompLifting (f : A ⟶ B) (g : B ⟶ C) :
    Localization.Lifting
      (DifferentialGradedModule.Derived.Q C)
      (DifferentialGradedModule.quasiIso C)
      ((f ≫ g).restrictDgFunctor.mapK ⋙
        DifferentialGradedModule.Derived.Q A)
      (restriction g ⋙ restriction f) :=
  ⟨restrictionCompFactors f g⟩

/-- Successive derived restrictions are canonically isomorphic to restriction along the
composite DGA map. -/
@[stacks 0BYX "composition coherence for derived restriction of scalars"]
noncomputable def restrictionCompIso (f : A ⟶ B) (g : B ⟶ C) :
    restriction g ⋙ restriction f ≅ restriction (f ≫ g) :=
  Localization.liftNatIso
    (DifferentialGradedModule.Derived.Q C)
    (DifferentialGradedModule.quasiIso C)
    ((f ≫ g).restrictDgFunctor.mapK ⋙
      DifferentialGradedModule.Derived.Q A)
    ((f ≫ g).restrictDgFunctor.mapK ⋙
      DifferentialGradedModule.Derived.Q A)
    (restriction g ⋙ restriction f) (restriction (f ≫ g)) (Iso.refl _)

/-- The identity functor, transported along identity restriction, is left adjoint to derived
restriction along the identity DGA map. -/
noncomputable def extensionIdAdjunction (A : CochainDGAlgebra.{u, v} R) :
    𝟭 (DifferentialGradedModule.Derived.Category A) ⊣ restriction (𝟙 A) :=
  (Adjunction.id :
    𝟭 (DifferentialGradedModule.Derived.Category A) ⊣
      𝟭 (DifferentialGradedModule.Derived.Category A)).ofNatIsoRight
        (restrictionIdIso A)

/-- Derived extension along an identity DGA map is canonically the identity. -/
@[stacks 0BYX "identity coherence for derived extension of scalars"]
noncomputable def extensionIdIso (A : CochainDGAlgebra.{u, v} R) :
    extension (𝟙 A) ≅
      𝟭 (DifferentialGradedModule.Derived.Category A) :=
  Adjunction.leftAdjointUniq (adjunction (𝟙 A)) (extensionIdAdjunction A)

/-- Successive derived extensions, transported along restriction composition, are left adjoint
to restriction along the composite map. -/
noncomputable def extensionCompAdjunction (f : A ⟶ B) (g : B ⟶ C) :
    extension f ⋙ extension g ⊣ restriction (f ≫ g) :=
  ((adjunction f).comp (adjunction g)).ofNatIsoRight
    (restrictionCompIso f g)

/-- Successive derived extensions are canonically isomorphic to extension along the composite
DGA map. -/
@[stacks 0BYX "composition coherence for derived extension of scalars"]
noncomputable def extensionCompIso (f : A ⟶ B) (g : B ⟶ C) :
    extension f ⋙ extension g ≅ extension (f ≫ g) :=
  Adjunction.leftAdjointUniq (extensionCompAdjunction f g)
    (adjunction (f ≫ g))

/-- The extension composition comparison is the mate determined by the transported adjunction
unit. -/
theorem extensionCompIso_hom_unit (f : A ⟶ B) (g : B ⟶ C) :
    (extensionCompAdjunction f g).unit ≫
        Functor.whiskerRight (extensionCompIso f g).hom
          (restriction (f ≫ g)) =
      (adjunction (f ≫ g)).unit := sorry

/-- The extension composition comparison is the mate determined by the transported adjunction
counit. -/
theorem extensionCompIso_hom_counit (f : A ⟶ B) (g : B ⟶ C) :
    Functor.whiskerLeft (restriction (f ≫ g))
        (extensionCompIso f g).hom ≫
      (adjunction (f ≫ g)).counit =
        (extensionCompAdjunction f g).counit := sorry

end Derived

end CochainDGAlgebra.Hom
