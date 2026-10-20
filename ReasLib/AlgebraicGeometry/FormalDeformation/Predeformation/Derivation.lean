module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Derivation
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.DualNumber

/-!
# Derivations and tangent vectors of predeformation functors

The canonical derivation-to-tangent map pushes the unique residue value forward
along the dual-number morphism associated to a derivation.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor.IsPredeformationFunctor

/-- The canonical map from residue-field derivations to tangent vectors sends a
derivation to the pushforward of the unique residue value. -/
def ofDerivation (F : ArtinianLocalAlgCat Λ k ⥤ Type v) [IsPredeformationFunctor F] :
    Derivation Λ k k → tangentSpace F :=
  fun D ↦ F.map (derivationToDualNumber D) (CategoryTheory.Functor.residuePoint F)

/-- The canonical tangent vector associated to a derivation is the pushforward of
any residue-field value along its dual-number morphism. -/
theorem ofDerivation_apply (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    [IsPredeformationFunctor F] (x0 : F.obj (residue Λ k)) (D : Derivation Λ k k) :
    ofDerivation F D = F.map (derivationToDualNumber D) x0 := sorry

/-- The canonical derivation-to-tangent map is linear over the residue field when
the predeformation functor satisfies Schlessinger's condition (H2). -/
theorem isLinearMap_ofDerivation (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    [IsPredeformationFunctor F] [HasSchlessingerH2 F] :
    IsLinearMap k (ofDerivation F) := sorry

/-- The canonical derivation-to-tangent map bundled as a linear map over the
residue field. -/
def ofDerivationLinear (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    [IsPredeformationFunctor F] [HasSchlessingerH2 F] :
    Derivation Λ k k →ₗ[k] tangentSpace F :=
  IsLinearMap.mk' (ofDerivation F) (isLinearMap_ofDerivation F)

/-- The bundled derivation-to-tangent map evaluates by the canonical pushforward
of the residue value. -/
theorem ofDerivationLinear_apply (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    [IsPredeformationFunctor F] [HasSchlessingerH2 F] (D : Derivation Λ k k) :
    ofDerivationLinear F D = ofDerivation F D := rfl

end CategoryTheory.Functor.IsPredeformationFunctor

end
