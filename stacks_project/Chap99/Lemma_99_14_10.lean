module

public import ReasLib.AlgebraicGeometry.Polarized.RimSchlessinger
public import ReasLib.AlgebraicGeometry.Polarized.Tangent
import StacksCheckRecall

/-!
# Finite-dimensional tangent and infinitesimal automorphism spaces of Polarized

For a polarized proper scheme over a field, the Artin deformation spaces at
finite-type field points and the geometric deformation spaces over arbitrary
fields are finite dimensional.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidsOver.Predeformation
open AlgebraicGeometry.Polarized

universe u

/- Lemma 99.14.10: The Artin tangent and infinitesimal automorphism spaces of a
polarized proper scheme at a finite-type field point, and its geometric tangent
and infinitesimal automorphism spaces over an arbitrary field, are finite dimensional. -/
@[stacks 0D4S] #check (AlgebraicGeometry.Polarized.finiteDimensional_tangentSpace :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ specZ)
    [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ specZ)
    [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : toGroupoidsOverSpecZ.p.Fiber (Over.mk kToS)),
    FiniteDimensional k
      (CategoryTheory.Functor.tangentSpace
        (predeformationFunctor toGroupoidsOverSpecZ openImmersion kToS h_factor x)))

@[stacks 0D4S] #check (AlgebraicGeometry.Polarized.finiteDimensional_infinitesimalAutomorphisms :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ specZ)
    [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ specZ)
    [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x : toGroupoidsOverSpecZ.p.Fiber (Over.mk kToS)),
    FiniteDimensional k
      (Functor.infinitesimalAutomorphisms
        (predeformationFunctor toGroupoidsOverSpecZ openImmersion kToS h_factor x)))

@[stacks 0D4S] #check (AlgebraicGeometry.Polarized.finiteDimensional_tangentAt :
    ∀ {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ specZ)
    (x : toGroupoidsOverSpecZ.p.Fiber (Over.mk kToS)),
    FiniteDimensional k ((tangentFunctor x).obj (ModuleCat.of k k)))

@[stacks 0D4S] #check (AlgebraicGeometry.Polarized.finiteDimensional_infAt :
    ∀ {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ specZ)
    (x : toGroupoidsOverSpecZ.p.Fiber (Over.mk kToS)),
    FiniteDimensional k ((infFunctor x).obj (ModuleCat.of k k)))
