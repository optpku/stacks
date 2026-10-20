module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ProjectiveCohomology
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.SchemeOverField CategoryTheory.Action.ModuleCat
open CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

universe u

section

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [GeometricallyConnected X.hom]
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
variable (ηbar : GeometricPoint (geometricBaseChange X))
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.left.Etale,
    HasWeakSheafify ((X.left.smallEtaleTopology).over U) (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ P : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback (geometricToArithmeticHom X)).op.HasLeftKanExtension P]
variable [(X.left.smallEtaleTopology).HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]
variable (M : (finiteTypeDiscreteModule Λ
    (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory)

section
variable [Projective X.hom]

/- Remark 64.29.2. On a projective curve, geometric H⁰ is naturally identified
with geometric fundamental-group invariants. -/
@[stacks 03VL] #check
  (AlgebraicGeometry.SchemeOverField.geometricH0_iso_pi1Invariants_natural X ηbar :
    ∃ i : ∀ M : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory,
        geometricH0Module X ηbar M ≅ geometricPi1Invariants X ηbar M,
      ∀ (M N : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory) (f : M ⟶ N),
        (i M).hom ≫ geometricPi1InvariantsMap X ηbar M f =
          geometricH0Map X ηbar M f ≫ (i N).hom)

end

variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [Etale (Compactification.Of.ι P)]

variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify
    (FieldExtension.baseChange k (AlgebraicClosure k)
      P.obj.right.hom).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [∀ G : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (smallEtalePullback
        (FieldExtension.toSource k (AlgebraicClosure k)
          P.obj.right.hom)).op.HasLeftKanExtension G]
section
variable [Projective X.hom]
variable (hΛ : IsUnit (Nat.card Λ : k))

#check (AlgebraicGeometry.SchemeOverField.geometricHc2_iso_coinvariantsTate_natural
    X ηbar P hΛ :
    ∃ i : ∀ M : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory,
        geometricHc2GaloisModule X ηbar M P ≅ geometricCoinvariantsTate X ηbar M hΛ,
      ∀ (M N : (finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory) (f : M ⟶ N),
        (i M).hom ≫ geometricCoinvariantsTateMap X ηbar M hΛ f =
          geometricHc2Map X ηbar M P f ≫ (i N).hom)

#check (AlgebraicGeometry.SchemeOverField.compactSupport_iso_geometricCoinvariantsTateTwist
    X ηbar M P hΛ :
    IsIsomorphic (geometricHc2GaloisModule X ηbar M P)
      (geometricCoinvariantsTate X ηbar M hΛ))

end

#check (AlgebraicGeometry.SchemeOverField.geometricHc0_isZero_of_not_projective
    X ηbar M P :
    ¬ Projective X.hom → IsZero (geometricHc0Module X ηbar M P))

end
