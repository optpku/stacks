module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.GeometricallyConnectedFiber.EtaleCover

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfFinitePresentation

/-
Lemma 37.46.3: a flat locally finitely presented morphism with geometrically reduced
fibres admits an étale cover whose members factor through étale base schemes by flat finitely
presented morphisms with geometrically connected and geometrically reduced fibres.
-/
@[stacks 0EY5] #check
  (AlgebraicGeometry.LocallyOfFinitePresentation.exists_etaleCover_factorization :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [LocallyOfFinitePresentation f] [Flat f] [GeometricallyReduced f],
      ∃ 𝒰 : X.Cover.{u} Scheme.etalePrecoverage, ∀ i : 𝒰.I₀,
        ∃ (Sᵢ : Scheme.{u}) (p : 𝒰.X i ⟶ Sᵢ) (q : Sᵢ ⟶ S)
          (h_etale : Etale q) (h_flat : Flat p)
          (h_finitePresentation : Scheme.Hom.FinitePresentation p)
          (h_connected : GeometricallyConnected p) (h_reduced : GeometricallyReduced p),
          p ≫ q = 𝒰.f i ≫ f)

end AlgebraicGeometry.LocallyOfFinitePresentation
