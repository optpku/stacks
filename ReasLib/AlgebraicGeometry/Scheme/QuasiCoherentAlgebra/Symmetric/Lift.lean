module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Symmetric
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Underlying

/-!
# The universal map from a symmetric algebra

This file constructs the morphism from the symmetric algebra of a quasi-coherent module sheaf
to a quasi-coherent algebra induced by a map into its underlying module.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SymmetricAlgebra

variable {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsQuasicoherent]
variable (A : S.QcAlgebraUnder)

/-- The objectwise symmetric-algebra map induced by a module-sheaf morphism into the
underlying module of a quasi-coherent algebra. -/
noncomputable def liftApp
    (f : ℱ ⟶ QcAlgebraUnder.underlyingModule S A)
    (U : (Opens S)ᵒᵖ) :
    PresheafOfModules.SymmetricAlgebra.commRingObj S.presheaf ℱ.val U ⟶
      A.obj.right.obj.obj U :=
  -- Local instance justification (defeq pin): SymmetricAlgebra.lift must use the algebra structure induced by the sectionwise structure map A.obj.hom.hom.app U.
  letI : Algebra (S.presheaf.obj U) (A.obj.right.obj.obj U) :=
    (A.obj.hom.hom.app U).hom.toAlgebra
  CommRingCat.ofHom
    (_root_.SymmetricAlgebra.lift
      (PresheafOfModules.SymmetricAlgebra.homApp S.presheaf f.val U).hom).toRingHom

/-- The objectwise symmetric-algebra lifts commute with restriction of sections. -/
theorem liftPresheaf_naturality
    (f : ℱ ⟶ QcAlgebraUnder.underlyingModule S A)
    {U V : (Opens S)ᵒᵖ} (g : U ⟶ V) :
    (PresheafOfModules.SymmetricAlgebra.commRingPresheaf S.presheaf ℱ.val).map g ≫
        liftApp ℱ A f V =
      liftApp ℱ A f U ≫ A.obj.right.obj.map g := sorry

/-- The sectionwise symmetric-algebra lifts form a morphism of presheaves of commutative
rings. -/
noncomputable def liftPresheaf
    (f : ℱ ⟶ QcAlgebraUnder.underlyingModule S A) :
    PresheafOfModules.SymmetricAlgebra.commRingPresheaf S.presheaf ℱ.val ⟶
      A.obj.right.obj where
  app U := liftApp ℱ A f U
  naturality _ _ g := liftPresheaf_naturality ℱ A f g

/-- The morphism of commutative-ring sheaves obtained by descending the sectionwise
symmetric-algebra lift through sheafification. -/
noncomputable def liftSheaf
    (f : ℱ ⟶ QcAlgebraUnder.underlyingModule S A) :
    sheaf ℱ ⟶ A.obj.right :=
  ⟨sheafifyLift (Opens.grothendieckTopology S) (liftPresheaf ℱ A f)
      A.obj.right.property⟩

/-- The symmetric-algebra lift commutes with the structure maps from the structure sheaf. -/
theorem lift_comp_structureMap
    (f : ℱ ⟶ QcAlgebraUnder.underlyingModule S A) :
    structureMap ℱ ≫ liftSheaf ℱ A f = A.obj.hom := sorry

/-- The degree-one inclusion into the underlying module of the symmetric algebra. -/
noncomputable def ι :
    ℱ ⟶ QcAlgebraUnder.underlyingModule S (qcAlgebra ℱ) :=
  AlgebraicGeometry.RingedSpace.SymmetricAlg.ι ℱ ≫
    eqToHom (underlyingModule_eq ℱ).symm

/-- A module-sheaf map into a quasi-coherent algebra extends canonically to a morphism from
the corresponding symmetric algebra. -/
noncomputable def lift
    (f : ℱ ⟶ QcAlgebraUnder.underlyingModule S A) : qcAlgebra ℱ ⟶ A :=
  ⟨Under.homMk (liftSheaf ℱ A f) (lift_comp_structureMap ℱ A f)⟩

/-- The symmetric-algebra lift restricts to the original map on degree-one generators. -/
theorem lift_ι
    (f : ℱ ⟶ QcAlgebraUnder.underlyingModule S A) :
    ι ℱ ≫ QcAlgebraUnder.underlyingModuleMap S (lift ℱ A f) = f := sorry

end AlgebraicGeometry.Scheme.SymmetricAlgebra
