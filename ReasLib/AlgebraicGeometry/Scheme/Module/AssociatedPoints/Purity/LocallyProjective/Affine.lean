/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.LocallyProjective
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Affine

/-!
# Purity and projectivity for affine schemes

This file specializes the relation between relative purity and local projectivity to modules
over finitely presented algebras.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

section SpecMapFinitePresentation

-- Local instance justification (proof-local temporary data): expose the explicit spectrum-map finite-presentation theorem only while elaborating this affine corollary.
attribute [local instance] AlgebraicGeometry.Scheme.Hom.finitePresentation_specMap

/-- For a finitely presented algebra and a finitely presented module flat over the base,
projectivity over the base is equivalent to relative purity of the associated module sheaf. -/
theorem module_projective_iff_tilde_isPureOver
    {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] [Module.FinitePresentation B N] [Module.Flat A N] :
    Module.Projective A N ↔
      (tilde (ModuleCat.of B N)).IsPureOver
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) := sorry

end SpecMapFinitePresentation

end AlgebraicGeometry.Scheme.Modules
