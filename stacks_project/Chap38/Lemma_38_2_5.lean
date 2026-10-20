module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Henselization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u v w x y z

namespace IsHenselizationOf

/- Lemma 38.2.5 (1): flatness of a strict-henselization module over the stalk, a
compatible henselization, and the strict henselization. -/
@[stacks 05VL] #check (IsHenselizationOf.moduleFlat_tfae :
  ∀ (S : Scheme.{u}) (s : S)
    (Rh : Type v) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh]
    (Rsh : Type w) [CommRing Rsh] [Algebra (S.presheaf.stalk s) Rsh] [Algebra Rh Rsh]
    [IsScalarTower (S.presheaf.stalk s) Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    [IsStrictHenselizationOf (S.presheaf.stalk s) Rsh]
    (Msh : Type x) [AddCommGroup Msh] [Module Rsh Msh],
    List.TFAE [
      Module.FlatAlong (algebraMap (S.presheaf.stalk s) Rsh) Msh,
      Module.FlatAlong (algebraMap Rh Rsh) Msh,
      Module.Flat Rsh Msh])

/- Lemma 38.2.5 (2): the five equivalent flatness conditions after one specified
base change from a compatible henselization to the strict henselization. -/
@[stacks 05VL] #check (IsHenselizationOf.moduleFlat_tfae_of_baseChange :
  ∀ (S : Scheme.{u}) (s : S)
    (Rh : Type v) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh]
    (Rsh : Type w) [CommRing Rsh] [Algebra (S.presheaf.stalk s) Rsh] [Algebra Rh Rsh]
    [IsScalarTower (S.presheaf.stalk s) Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    [IsStrictHenselizationOf (S.presheaf.stalk s) Rsh]
    (Mh : Type y) [AddCommGroup Mh] [Module Rh Mh]
    (Msh : Type x) [AddCommGroup Msh] [Module Rh Msh] [Module Rsh Msh]
    [IsScalarTower Rh Rsh Msh]
    (g : Mh →ₗ[Rh] Msh) (hg : IsBaseChange Rsh g),
    List.TFAE [
      Module.FlatAlong (algebraMap (S.presheaf.stalk s) Rsh) Msh,
      Module.FlatAlong (algebraMap Rh Rsh) Msh,
      Module.Flat Rsh Msh,
      Module.FlatAlong (algebraMap (S.presheaf.stalk s) Rh) Mh,
      Module.Flat Rh Mh])

/- Lemma 38.2.5 (3): the six equivalent flatness conditions after specified successive
base changes from the stalk through a henselization to the strict henselization. -/
@[stacks 05VL] #check (IsHenselizationOf.moduleFlat_tfae_of_iteratedBaseChange :
  ∀ (S : Scheme.{u}) (s : S)
    (Rh : Type v) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh]
    (Rsh : Type w) [CommRing Rsh] [Algebra (S.presheaf.stalk s) Rsh] [Algebra Rh Rsh]
    [IsScalarTower (S.presheaf.stalk s) Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    [IsStrictHenselizationOf (S.presheaf.stalk s) Rsh]
    (M : Type z) [AddCommGroup M] [Module (S.presheaf.stalk s) M]
    (Mh : Type y) [AddCommGroup Mh] [Module (S.presheaf.stalk s) Mh] [Module Rh Mh]
    [IsScalarTower (S.presheaf.stalk s) Rh Mh]
    (Msh : Type x) [AddCommGroup Msh] [Module Rh Msh] [Module Rsh Msh]
    [IsScalarTower Rh Rsh Msh]
    (f : M →ₗ[S.presheaf.stalk s] Mh) (hf : IsBaseChange Rh f)
    (g : Mh →ₗ[Rh] Msh) (hg : IsBaseChange Rsh g),
    List.TFAE [
      Module.FlatAlong (algebraMap (S.presheaf.stalk s) Rsh) Msh,
      Module.FlatAlong (algebraMap Rh Rsh) Msh,
      Module.Flat Rsh Msh,
      Module.FlatAlong (algebraMap (S.presheaf.stalk s) Rh) Mh,
      Module.Flat Rh Mh,
      Module.Flat (S.presheaf.stalk s) M])

end IsHenselizationOf
