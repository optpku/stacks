module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.InfinitesimalLifting

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.12.2: a locally finite type morphism to a locally Noetherian scheme is smooth
if and only if every commutative square arising from a small extension of Artinian local rings,
whose bottom morphism is of finite type, admits a lift making both triangles commute. -/
@[stacks 02HY]
#check (AlgebraicGeometry.Scheme.Hom.smooth_iff_smallExtensionLifting :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f],
    Smooth f ↔
      ∀ (B' B : Type u) [CommRing B'] [CommRing B]
        (π : B' →+* B) [π.IsSmallExtension]
        (α : Spec (CommRingCat.of B) ⟶ X) (β : Spec (CommRingCat.of B') ⟶ S)
        [FiniteType β],
        CommSq α (Spec.map (CommRingCat.ofHom π)) f β →
          ∃ γ : Spec (CommRingCat.of B') ⟶ X,
            Spec.map (CommRingCat.ofHom π) ≫ γ = α ∧ γ ≫ f = β)

end AlgebraicGeometry.Scheme.Hom
