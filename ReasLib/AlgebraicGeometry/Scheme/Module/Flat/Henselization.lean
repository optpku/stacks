/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.IsTensorProduct
public import ReasLib.Algebra.Module.Flat.Relative
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry

universe u v w x y z

namespace IsHenselizationOf

/-- Flatness of a module over a strict henselization of a scheme stalk is equivalent
over the stalk, a compatible henselization, and the strict henselization. -/
@[stacks 05VL]
theorem moduleFlat_tfae (S : Scheme.{u}) (s : S)
    (Rh : Type v) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh]
    (Rsh : Type w) [CommRing Rsh] [Algebra (S.presheaf.stalk s) Rsh] [Algebra Rh Rsh]
    [IsScalarTower (S.presheaf.stalk s) Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    [IsStrictHenselizationOf (S.presheaf.stalk s) Rsh]
    (Msh : Type x) [AddCommGroup Msh] [Module Rsh Msh] :
    List.TFAE [
      Module.FlatAlong (algebraMap (S.presheaf.stalk s) Rsh) Msh,
      Module.FlatAlong (algebraMap Rh Rsh) Msh,
      Module.Flat Rsh Msh] := sorry

/-- If an `Rh`-module becomes an `Rsh`-module by base change, its flatness over a scheme
stalk and `Rh` joins the equivalent flatness conditions over a compatible henselization and
strict henselization. -/
@[stacks 05VL]
theorem moduleFlat_tfae_of_baseChange (S : Scheme.{u}) (s : S)
    (Rh : Type v) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
    [IsHenselizationOf (S.presheaf.stalk s) Rh]
    (Rsh : Type w) [CommRing Rsh] [Algebra (S.presheaf.stalk s) Rsh] [Algebra Rh Rsh]
    [IsScalarTower (S.presheaf.stalk s) Rh Rsh] [IsLocalHom (algebraMap Rh Rsh)]
    [IsStrictHenselizationOf (S.presheaf.stalk s) Rsh]
    (Mh : Type y) [AddCommGroup Mh] [Module Rh Mh]
    (Msh : Type x) [AddCommGroup Msh] [Module Rh Msh] [Module Rsh Msh]
    [IsScalarTower Rh Rsh Msh]
    (g : Mh →ₗ[Rh] Msh) (hg : IsBaseChange Rsh g) :
    List.TFAE [
      Module.FlatAlong (algebraMap (S.presheaf.stalk s) Rsh) Msh,
      Module.FlatAlong (algebraMap Rh Rsh) Msh,
      Module.Flat Rsh Msh,
      Module.FlatAlong (algebraMap (S.presheaf.stalk s) Rh) Mh,
      Module.Flat Rh Mh] := sorry

/-- For modules obtained by successive base changes from a scheme stalk through a compatible
henselization to a strict henselization, flatness of the original module is equivalent to
flatness of either base-changed module over each relevant ring. -/
@[stacks 05VL]
theorem moduleFlat_tfae_of_iteratedBaseChange (S : Scheme.{u}) (s : S)
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
    (g : Mh →ₗ[Rh] Msh) (hg : IsBaseChange Rsh g) :
    List.TFAE [
      Module.FlatAlong (algebraMap (S.presheaf.stalk s) Rsh) Msh,
      Module.FlatAlong (algebraMap Rh Rsh) Msh,
      Module.Flat Rsh Msh,
      Module.FlatAlong (algebraMap (S.presheaf.stalk s) Rh) Mh,
      Module.Flat Rh Mh,
      Module.Flat (S.presheaf.stalk s) M] := sorry

end IsHenselizationOf
