module

public import ReasLib.Algebra.Module.Injective.FlatLocal
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 47.7.4: Let `f : R →+* S` be a flat local homomorphism of Noetherian local
rings such that the induced map
`R ⧸ IsLocalRing.maximalIdeal R →+* S ⧸ (IsLocalRing.maximalIdeal R).map f` is an
isomorphism. Then any injective hull of the residue field of `R` is isomorphic, as an
`R`-module, to the restriction of scalars of any injective hull of the residue field of
`S`. -/
@[stacks 08Z5] #check
  (LinearMap.IsInjectiveHull.nonempty_iso_restrictScalars_of_flat_local :
    ∀ {R : Type u} {S : Type v} {ER ES : Type w}
      [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
      [AddCommGroup ER] [Module R ER] [Module.Injective R ER]
      [AddCommGroup ES] [Module S ES] [Module.Injective S ES]
      (f : R →+* S) [IsLocalHom f] (hflat : f.Flat)
      (hres : Function.Bijective
        (Ideal.quotientMap ((IsLocalRing.maximalIdeal R).map f) f Ideal.le_comap_map))
      (iotaR : IsLocalRing.ResidueField R →ₗ[R] ER) (hiotaR : iotaR.IsInjectiveHull)
      (iotaS : IsLocalRing.ResidueField S →ₗ[S] ES) (hiotaS : iotaS.IsInjectiveHull),
      Nonempty
        (ModuleCat.of R ER ≅
          (ModuleCat.restrictScalars f).obj (ModuleCat.of S ES)))
