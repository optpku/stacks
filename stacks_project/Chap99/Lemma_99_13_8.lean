module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper.FiniteDimensional
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Spaces
open AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids

universe u

/- Lemma 99.13.8: Artin tangent finiteness with the finite-module affine-chart premise. -/
@[stacks 0D1K] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.finiteDimensional_tangentSpace :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : (pFpFlatProperGroupoids S).Fiber (Over.mk kToS)),
   FiniteDimensional k (tangentSpace openImmersion kToS h_factor x))

/- Lemma 99.13.8: Artin infinitesimal automorphism finiteness with the same chart assumptions. -/
@[stacks 0D1K] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.finiteDimensional_infinitesimalAutomorphisms :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : (pFpFlatProperGroupoids S).Fiber (Over.mk kToS)),
   FiniteDimensional k (infinitesimalAutomorphisms openImmersion kToS h_factor x))

/- Lemma 99.13.8: RS* tangent finiteness over an arbitrary field. -/
@[stacks 0D1K] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.finiteDimensional_tangentAt :
  ∀ {S : Scheme.{u}} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    (x : (pFpFlatProperGroupoids S).Fiber (Over.mk kToS)),
   FiniteDimensional k (tangentAt kToS x))

/- Lemma 99.13.8: RS* infinitesimal automorphism finiteness over an arbitrary field. -/
@[stacks 0D1K] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.finiteDimensional_infAt :
  ∀ {S : Scheme.{u}} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S)
    (x : (pFpFlatProperGroupoids S).Fiber (Over.mk kToS)),
   FiniteDimensional k (infAt kToS x))

