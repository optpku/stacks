module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.AffineBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.ClosedImmersion

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a closed immersion of algebraic spaces over `B` and quasi-coherent modules,
the relative Hom functors `Hom(F, i_* G')` and `Hom(i^* F, G')` are naturally
isomorphic on schemes over `B`. -/
theorem homFunctor_closedImmersion {S : Scheme.{u}} {B X X' : AlgebraicSpace S}
    (f : X ⟶ B) (f' : X' ⟶ B) (i : X' ⟶ X) (h_over : i ≫ f = f')
    [IsClosedImmersion i] (F : X.Modules) (G' : X'.Modules)
    [F.IsQuasicoherent] [G'.IsQuasicoherent] :
    IsIsomorphic (homFunctor f F ((pushforward i).obj G'))
      (homFunctor f' ((pullback i).obj F) G') :=
  sorry

/-- At each scheme over `B`, the Hom-types of the base-changed quasi-coherent modules
for a closed immersion are equivalent under pullback-pushforward adjunction. -/
theorem homFunctor_closedImmersion_obj {S : Scheme.{u}} {B X X' : AlgebraicSpace S}
    (f : X ⟶ B) (f' : X' ⟶ B) (i : X' ⟶ X) (h_over : i ≫ f = f')
    [IsClosedImmersion i] (F : X.Modules) (G' : X'.Modules)
    [F.IsQuasicoherent] [G'.IsQuasicoherent] (σ : SchemeOver B) :
    Nonempty
      ((baseChangeModule f σ.hom F ⟶ baseChangeModule f σ.hom ((pushforward i).obj G')) ≃
        (baseChangeModule f' σ.hom ((pullback i).obj F) ⟶ baseChangeModule f' σ.hom G')) := by
  rcases homFunctor_closedImmersion f f' i h_over F G' with ⟨e⟩
  exact ⟨CategoryTheory.Iso.toEquiv (e.app (op σ))⟩

end AlgebraicGeometry.AlgebraicSpace.Modules
