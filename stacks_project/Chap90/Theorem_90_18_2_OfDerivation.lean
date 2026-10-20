module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Derivation

/-!
# Canonical map from derivations to a functor tangent space

The canonical derivation map and its linear companion are provided by the shared
predeformation API. The residue-point abbreviation preserves the existing source API.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat TrivSqZeroExt
open CategoryTheory.Functor.IsPredeformationFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor.IsPredeformationFunctor

/-- The unique residue-field value of a predeformation functor. -/
abbrev residuePoint (F : ArtinianLocalAlgCat Λ k ⥤ Type v) [IsPredeformationFunctor F] :
    F.obj (residue Λ k) :=
  CategoryTheory.Functor.residuePoint F

end CategoryTheory.Functor.IsPredeformationFunctor

#check (ArtinianLocalAlgCat.derivationToDualNumber :
  Derivation Λ k k → (residue Λ k ⟶ dualNumber Λ k))

#check (ArtinianLocalAlgCat.derivationToDualNumber_apply :
  ∀ (D : Derivation Λ k k) (a : k),
    (derivationToDualNumber D).hom a = inl a + inr (D a))

variable (F : ArtinianLocalAlgCat Λ k ⥤ Type v) [CategoryTheory.Functor.IsPredeformationFunctor F]

#check (CategoryTheory.Functor.residuePoint :
  ∀ (G : ArtinianLocalAlgCat Λ k ⥤ Type v) [CategoryTheory.Functor.IsPredeformationFunctor G],
    G.obj (residue Λ k))

#check (CategoryTheory.Functor.residuePoint_spec F :
  ∀ x : F.obj (residue Λ k), x = CategoryTheory.Functor.residuePoint F)

#check (CategoryTheory.Functor.IsPredeformationFunctor.ofDerivation F :
  Derivation Λ k k → tangentSpace F)

#check (CategoryTheory.Functor.IsPredeformationFunctor.ofDerivation_apply F :
  ∀ (x0 : F.obj (residue Λ k)) (D : Derivation Λ k k),
    ofDerivation F D = F.map (derivationToDualNumber D) x0)

variable [CategoryTheory.Functor.HasSchlessingerH2 F]

#check (CategoryTheory.Functor.IsPredeformationFunctor.isLinearMap_ofDerivation F :
  IsLinearMap k (ofDerivation F))

#check (CategoryTheory.Functor.IsPredeformationFunctor.ofDerivationLinear F :
  Derivation Λ k k →ₗ[k] tangentSpace F)

#check (CategoryTheory.Functor.IsPredeformationFunctor.ofDerivationLinear_apply F :
  ∀ D : Derivation Λ k k, ofDerivationLinear F D = ofDerivation F D)

end
