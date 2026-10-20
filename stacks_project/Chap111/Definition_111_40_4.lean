module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Affine
public import ReasLib.RingTheory.PicardGroup.Invertible
import StacksCheckRecall

@[expose] public section

universe u

section

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/- Definition 111.40.4 (1): an `R`-module `M` is invertible if `tilde M` is an invertible sheaf
on `Spec R`. -/
@[stacks 02AG]
#check (AlgebraicGeometry.Scheme.Modules.tilde_invertible_iff_module_invertible M :
    AlgebraicGeometry.Scheme.Modules.Invertible (AlgebraicGeometry.tilde M) ↔
      Module.Invertible R M)

end

section

variable {R : Type u} [CommRing R] (M : ModuleCat R)

/- Definition 111.40.4 (2): an `R`-module `M` is trivial if it is isomorphic to `R` as an
`R`-module. -/
@[stacks 02AG]
#check (ModuleCat.isUnitObject_iff_linearEquiv M :
    CategoryTheory.MonoidalCategory.isUnitObject M ↔ Nonempty (M ≃ₗ[R] R))

#check (Module.Invertible.iff_finiteLocallyFreeOfRank_one :
    Module.Invertible R M ↔ Module.FiniteLocallyFreeOfRank R M 1)

end
