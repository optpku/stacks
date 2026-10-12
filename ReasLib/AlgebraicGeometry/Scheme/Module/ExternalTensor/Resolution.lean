/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For finite-type schemes over a Noetherian ring with the resolution property,
every coherent module on their fiber product admits an epimorphism from an external
tensor product of finite locally free modules. -/
theorem exists_epi_from_externalTensorProduct
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R))
    [Scheme.Hom.FiniteType f] [Scheme.Hom.FiniteType g]
    (hX : Scheme.HasResolutionProperty X)
    (hY : Scheme.HasResolutionProperty Y)
    (F : (Limits.pullback f g).Modules) [F.IsCoherent] :
    ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree)
      (G : Y.Modules) (_ : G.IsFiniteLocallyFree)
      (q : externalTensorProduct f g E G ⟶ F), Epi q := sorry

/-- For quasi-compact, quasi-separated schemes over a ring with the resolution
property, every finite-type quasi-coherent module on their fiber product admits
an epimorphism from an external tensor product of finite locally free modules. -/
theorem exists_epi_from_externalTensorProduct_of_qcqs
    {R : Type u} [CommRing R]
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R))
    (hX : Scheme.HasResolutionProperty X)
    (hY : Scheme.HasResolutionProperty Y)
    (F : (Limits.pullback f g).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree)
      (G : Y.Modules) (_ : G.IsFiniteLocallyFree)
      (q : externalTensorProduct f g E G ⟶ F), Epi q := sorry

end AlgebraicGeometry.Scheme.Modules
