module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor.Resolution
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 57.9.2: for quasi-compact, quasi-separated schemes over a ring with the
resolution property, every finite-type quasi-coherent module on their fiber product
admits an epimorphism from an external tensor product of finite locally free modules. -/
@[stacks 0FZ1] #check
  (AlgebraicGeometry.Scheme.Modules.exists_epi_from_externalTensorProduct_of_qcqs :
    ∀ {R : Type u} [CommRing R]
      {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y] [QuasiSeparatedSpace Y]
      (f : X ⟶ Spec (CommRingCat.of R))
      (g : Y ⟶ Spec (CommRingCat.of R))
      (hX : Scheme.HasResolutionProperty X)
      (hY : Scheme.HasResolutionProperty Y)
      (F : (Limits.pullback f g).Modules) [F.IsQuasicoherent] [F.IsFiniteType],
      ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree)
        (G : Y.Modules) (_ : G.IsFiniteLocallyFree)
        (q : externalTensorProduct f g E G ⟶ F), Epi q)

end AlgebraicGeometry.Scheme.Modules
