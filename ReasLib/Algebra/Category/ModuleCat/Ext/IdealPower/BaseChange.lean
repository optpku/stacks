module

public import ReasLib.Algebra.Category.ModuleCat.Ext.FlatBaseChange.Coproduct
public import ReasLib.Algebra.Category.ModuleCat.Ext.FlatBaseChange.Epi
public import ReasLib.Algebra.Category.ModuleCat.Ext.IdealQuotient.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.IdealPower.BaseChange
public import ReasLib.Algebra.Module.IdealPower.Cover

/-!
# Ext Base Change for Ideal-Power Torsion Modules

@stack 05EG

For a flat ring map inducing an isomorphism modulo a finitely generated ideal,
the direct base-change map on Ext is an isomorphism when the source is supported
on powers of that ideal.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u

namespace CategoryTheory.ModuleCat.Ext.IdealPower.BaseChange

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Tag 05EG: flat base change on `Ext¹` is bijective for the canonical direct-sum cover by
positive ideal-power quotients. -/
@[stacks 05EG "Ext base change on the canonical ideal-power quotient cover"]
theorem cover_map_bijective (f : R →+* S) (I : Ideal R) (hI : I.FG)
    (M N : ModuleCat.{u} R) (hf : f.Flat)
    (hquot : Function.Bijective (f.quotientByIdeal I)) :
    Function.Bijective
      (FlatBaseChange.map f (ModuleCat.IdealPower.Cover.source I M) N hf 1) := sorry

/-- Tag 05EG: flat base change on `Ext¹(M, N)` is injective for every ideal-power-torsion
source `M`. -/
@[stacks 05EG "injective Ext base change for ideal-power torsion"]
theorem map_injective (f : R →+* S) (I : Ideal R) (hI : I.FG)
    (M N : ModuleCat.{u} R) (hf : f.Flat)
    (hM : Module.IsIdealPowerTorsion I M)
    (hquot : Function.Bijective (f.quotientByIdeal I)) :
    Function.Injective (FlatBaseChange.map f M N hf 1) := sorry

/-- Tag 05EG: flat base change on `Ext¹(M, N)` is surjective for every ideal-power-torsion
source `M`. -/
@[stacks 05EG "surjective Ext base change for ideal-power torsion"]
theorem map_surjective (f : R →+* S) (I : Ideal R) (hI : I.FG)
    (M N : ModuleCat.{u} R) (hf : f.Flat)
    (hM : Module.IsIdealPowerTorsion I M)
    (hquot : Function.Bijective (f.quotientByIdeal I)) :
    Function.Surjective (FlatBaseChange.map f M N hf 1) := sorry

/-- Tag 05EG: if a flat ring map is an isomorphism modulo a finitely generated ideal, then
base change on `Ext¹(M, N)` is bijective for every ideal-power-torsion source `M`. -/
@[stacks 05EG]
theorem map_bijective (f : R →+* S) (I : Ideal R) (hI : I.FG)
    (M N : ModuleCat.{u} R) (hf : f.Flat)
    (hM : Module.IsIdealPowerTorsion I M)
    (hquot : Function.Bijective (f.quotientByIdeal I)) :
    Function.Bijective (FlatBaseChange.map f M N hf 1) := sorry

end CategoryTheory.ModuleCat.Ext.IdealPower.BaseChange
