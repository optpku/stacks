module

public import stacks_project.Chap90.Definition_90_10_1_Schlessinger
public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Lemma_90_10_5_Associated
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Lemma_98_3_1
import Mathlib.Tactic.CrossRefAttribute

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

/-- The predeformation functor of 98.3.0.2 is cofibered in groupoids, so the
associated functor of isomorphism classes is defined. -/
instance instIsFiberedInGroupoids_predeformationFunctor
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (X : GroupoidsOver S)
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS)) :
    Functor.IsFibered.InGroupoids
      (predeformationFunctor X openImmersion kToS h_factor x0).op :=
  sorry

/-- Remark 98.6.2 (1): if the predeformation functor
`p = predeformationFunctor X openImmersion kToS h_factor x0` of 98.3.0.2 is a
deformation category, equivalently if it satisfies (RS) (since `p` is already a
predeformation category by 98.3.1), then `p` satisfies Schlessinger's condition
(S1). In particular this applies when `X` satisfies (RS), by Lemma 98.6.1. -/
@[stacks 07WV]
instance instHasSchlessingerS1_predeformationFunctor
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (X : GroupoidsOver S)
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS))
    [Functor.HasRimSchlessinger (predeformationFunctor X openImmersion kToS h_factor x0)] :
    Functor.HasSchlessingerS1 (predeformationFunctor X openImmersion kToS h_factor x0) :=
  sorry

/-- Remark 98.6.2 (2): if the predeformation functor
`p = predeformationFunctor X openImmersion kToS h_factor x0` of 98.3.0.2 is a
deformation category, equivalently if it satisfies (RS) (since `p` is already a
predeformation category by 98.3.1), then `p` satisfies Schlessinger's condition
(S2). In particular this applies when `X` satisfies (RS), by Lemma 98.6.1. -/
@[stacks 07WV]
instance instHasSchlessingerS2_predeformationFunctor
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (X : GroupoidsOver S)
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS))
    [Functor.HasRimSchlessinger (predeformationFunctor X openImmersion kToS h_factor x0)] :
    Functor.HasSchlessingerS2 (predeformationFunctor X openImmersion kToS h_factor x0) :=
  sorry

/-- Remark 98.6.2 (3): if the predeformation functor
`p = predeformationFunctor X openImmersion kToS h_factor x0` of 98.3.0.2 is a
deformation category, equivalently if it satisfies (RS) (since `p` is already a
predeformation category by 98.3.1), then the functor of isomorphism classes
`CategoryOfElements.π (Functor.isoClassFunctor p)` (Remarks 90.5.2 (10))
satisfies (S1). In particular this applies when `X` satisfies (RS), by
Lemma 98.6.1. -/
@[stacks 07WV]
instance instHasSchlessingerS1_isoClass_predeformationFunctor
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (X : GroupoidsOver S)
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS))
    [Functor.HasRimSchlessinger (predeformationFunctor X openImmersion kToS h_factor x0)] :
    Functor.HasSchlessingerS1
      (CategoryOfElements.π (Functor.isoClassFunctor
        (predeformationFunctor X openImmersion kToS h_factor x0))) :=
  sorry

/-- Remark 98.6.2 (4): if the predeformation functor
`p = predeformationFunctor X openImmersion kToS h_factor x0` of 98.3.0.2 is a
deformation category, equivalently if it satisfies (RS) (since `p` is already a
predeformation category by 98.3.1), then the functor of isomorphism classes
`CategoryOfElements.π (Functor.isoClassFunctor p)` (Remarks 90.5.2 (10))
satisfies (S2). In particular this applies when `X` satisfies (RS), by
Lemma 98.6.1. -/
@[stacks 07WV]
instance instHasSchlessingerS2_isoClass_predeformationFunctor
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (X : GroupoidsOver S)
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS))
    [Functor.HasRimSchlessinger (predeformationFunctor X openImmersion kToS h_factor x0)] :
    Functor.HasSchlessingerS2
      (CategoryOfElements.π (Functor.isoClassFunctor
        (predeformationFunctor X openImmersion kToS h_factor x0))) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
