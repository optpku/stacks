module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommIntrinsicDual
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.GeometricPoint
noncomputable section
universe u

namespace NoncommIntrinsicDualTransport

/-- Rebundle a specified additive equivalence with its scalar restriction law.
This keeps nested sheaf/module instance elaboration out of the data map. -/
def restrictionIso {A B : Type*} [Ring A] [Ring B] (h : A →+* B)
    (N : ModuleCat.{u + 1} B) (M : ModuleCat.{u + 1} A) (e : N ≃+ M)
    (he : ∀ (a : A) (x : N), e (h a • x) = a • e x) :
    (ModuleCat.restrictScalars h).obj N ≅ M :=
  -- Local instance justification (defeq pin): this is exactly the source action of restrictScalars h.
  letI := Module.compHom N h
  (show (ModuleCat.restrictScalars h).obj N ≃ₗ[A] M from
    { __ := e
      map_smul' := he }).toModuleIso

variable (R : Type (u + 1)) [Ring R] [Finite R]

/-- The central integer-quotient map into the opposite ring. Its multiplicativity
uses centrality, not an invalid generic map R→Rᵐᵒᵖ. -/
def rightScalarHom : ActualRootsModule.Coeff.{u} (Nat.card R) →+* Rᵐᵒᵖ where
  toFun a := MulOpposite.op (NoncommFiniteCoefficient.scalarHom R a)
  map_zero' := by sorry
  map_one' := by sorry
  map_add' := by sorry
  map_mul' := by sorry

/-- Restrict only along the specified central coefficient homomorphism. -/
abbrev modules := ModuleCat.restrictScalars (rightScalarHom R)

instance modules_preservesPointColimits : PreservesFilteredColimitsOfSize.{u,u}
    (modules R : ModuleCat.{u + 1} Rᵐᵒᵖ ⥤
      ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R))) := by sorry

variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommFiniteCoefficient.modules R)]
variable [Y.smallEtaleTopology.HasSheafCompose (modules R)]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))

/-- Forgetting the right action recovers precisely the original A-linear
local-Hom sheaf, by identity on actual local morphisms. -/
def underlyingIso :
    (sheafCompose Y.smallEtaleTopology (modules R)).obj (NoncommIntrinsicDual.obj R Y F) ≅
      NoncommFiniteCoefficient.dual R Y F where
  hom := ObjectProperty.homMk
    { app := fun U ↦
        (restrictionIso (rightScalarHom R) ((NoncommIntrinsicDual.obj R Y F).obj.obj U)
          ((NoncommFiniteCoefficient.dual R Y F).obj.obj U) (AddEquiv.refl _) (by sorry)).hom
      naturality := by sorry }
  inv := ObjectProperty.homMk
    { app := fun U ↦
        (restrictionIso (rightScalarHom R) ((NoncommIntrinsicDual.obj R Y F).obj.obj U)
          ((NoncommFiniteCoefficient.dual R Y F).obj.obj U) (AddEquiv.refl _) (by sorry)).inv
      naturality := by sorry }
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- Exact scalar restriction through the actual filtered stalk, followed by
the identity on local-Hom sections. -/
def stalkIso (x : GeometricPoint Y) :
    (modules R).obj ((StalkRepresentation.stalk Rᵐᵒᵖ x).obj (NoncommIntrinsicDual.obj R Y F)) ≅
    (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} (Nat.card R)) x).obj
      (NoncommFiniteCoefficient.dual R Y F) :=
  (((geometricPointEtalePoint x).presheafFiberCompIso
    (modules R : ModuleCat.{u + 1} Rᵐᵒᵖ ⥤
      ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R)))).app
      (NoncommIntrinsicDual.obj R Y F).obj).symm ≪≫
    (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} (Nat.card R)) x).mapIso
      (underlyingIso R Y F)

end NoncommIntrinsicDualTransport
