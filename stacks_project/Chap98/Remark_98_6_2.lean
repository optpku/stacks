module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Projection
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Associated
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
import StacksCheckRecall

/-!
# Schlessinger conditions for predeformation functors

If the predeformation functor `p : ℱ_{X, k, x0} ⥤ ArtinianLocalAlgCat Λ k` of
98.3.0.2 is a deformation category, equivalently if it satisfies (RS), then it
satisfies Schlessinger's conditions (S1) and (S2), as does the associated
functor of isomorphism classes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (X : GroupoidsOver S)
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS))

-- The predeformation projection is unconditionally cofibered in groupoids.
#check (CategoryTheory.Functor.IsPredeformationCategory.isCofiberedInGroupoids :
  Functor.IsFibered.InGroupoids
    (predeformationFunctor X openImmersion kToS h_factor x0).op)

variable [Functor.HasRimSchlessinger
  (predeformationFunctor X openImmersion kToS h_factor x0)]

/- Remark 98.6.2: If the predeformation category satisfies (RS), then it satisfies
Schlessinger's conditions (S1) and (S2), and its associated functor of
isomorphism classes also satisfies (S1) and (S2). In particular this applies
when X satisfies (RS), by Lemma 98.6.1. -/
@[stacks 07WV] #check (CategoryTheory.Functor.HasRimSchlessinger.toHasSchlessingerS1
  (predeformationFunctor X openImmersion kToS h_factor x0) :
  Functor.HasSchlessingerS1 (predeformationFunctor X openImmersion kToS h_factor x0))

#check (CategoryTheory.Functor.HasRimSchlessinger.toHasSchlessingerS2
  (predeformationFunctor X openImmersion kToS h_factor x0) :
  Functor.HasSchlessingerS2 (predeformationFunctor X openImmersion kToS h_factor x0))

#check (CategoryTheory.Functor.hasSchlessingerS1_isoClass
  (predeformationFunctor X openImmersion kToS h_factor x0) :
  Functor.HasSchlessingerS1
    (CategoryOfElements.π (Functor.isoClassFunctor
      (predeformationFunctor X openImmersion kToS h_factor x0))))

#check (CategoryTheory.Functor.hasSchlessingerS2_isoClass
  (predeformationFunctor X openImmersion kToS h_factor x0) (Or.inl inferInstance) :
  Functor.HasSchlessingerS2
    (CategoryOfElements.π (Functor.isoClassFunctor
      (predeformationFunctor X openImmersion kToS h_factor x0))))

end AlgebraicGeometry.GroupoidsOver.Predeformation
