module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FinitePresentation.DenseOpen
import StacksCheckRecall

/-!
# Extending finite presentation from a dense open of algebraic spaces

A finite-type quasicoherent module on an algebraic space, flat over a locally
finitely presented morphism, is finitely presented if its restriction above a
quasi-compact scheme-theoretically dense open of the base is finitely presented.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.37.1: A finite-type quasicoherent module flat over a locally finitely
presented morphism of algebraic spaces is finitely presented if its restriction above a
quasi-compact scheme-theoretically dense open subspace is finitely presented. -/
@[stacks 0876] #check
  (AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules.finitePresentation_of_restrict_of_flatOver :
    ∀ {S : Scheme.{u}} {X Y V : AlgebraicSpace S} (f : X ⟶ Y),
      SmallEtale.LocallyOfFinitePresentation f →
      ∀ (F : SmallEtale.Modules X),
        SmallEtale.Modules.IsQuasicoherent F → SmallEtale.Modules.IsFiniteType F →
        SmallEtale.Modules.FlatOver F f → ∀ (ι : V ⟶ Y)
          (h_open : Representable.IsOpenImmersion ι),
        Representable.QuasiCompact ι → Open.IsSchemeTheoreticallyDense ι →
        SmallEtale.Modules.IsFinitePresentation
          ((SmallEtale.Modules.restrict (Open.inverseImageι f ι h_open)
            (Representable.isOpenImmersion_etale (Open.inverseImageι f ι h_open)
              (Open.inverseImage_isOpenImmersion f ι h_open))).obj F) →
        SmallEtale.Modules.IsFinitePresentation F)
