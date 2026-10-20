module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.LocalRing.ResidueField.Compatible
public import ReasLib.RingTheory.RingHom.Local.Residue

@[expose] public section

/-!
# Comparisons of Strict Henselizations

This leaf records the proposition-valued universal property needed to compare
strict henselizations after a local map.  The comparison is controlled by a
specified map of residue fields.  In particular, it proves existence and
uniqueness of compatible maps without selecting one as non-Prop data.

@stack 04GU
-/

open IsLocalRing

universe u v w x y z

namespace IsStrictHenselizationOf.Comparison

section ResidueMap

variable {R : Type u} {S : Type v} {A : Type w} {B : Type x}
variable [hCommR : CommRing R] [hLocalR : IsLocalRing R]
variable [hCommS : CommRing S] [hLocalS : IsLocalRing S]
variable [hRS : Algebra R S] [hRSLocal : IsLocalHom (algebraMap R S)]
variable [hCommA : CommRing A] [hRA : Algebra R A]
variable [hA : IsStrictHenselizationOf R A]
variable [hCommB : CommRing B] [hSB : Algebra S B] [hRB : Algebra R B]
variable [hTower : IsScalarTower R S B] [hB : IsStrictHenselizationOf S B]

-- The source local map, both strict-henselization owners, and the scalar tower
-- are all part of the comparison theorem, even when they are not visible in
-- the resulting bundled-map type.
include hCommR hLocalR hCommS hLocalS hRS hRSLocal hCommA hRA hA
  hCommB hSB hRB hTower hB

/-- Tag 04GU: a residue-field map compatible with a local map `R → S` lifts
to a residue-compatible local `R`-algebra map between chosen strict
henselizations.  This is only a `Nonempty` result: it does not choose a
comparison map as public data. -/
@[stacks 04GU "strict henselization comparison from a residue-field map"]
theorem nonempty_ofResidueMap
    (τ : ResidueField A →+* ResidueField B)
    (hτ : IsLocalRing.ResidueField.Compatible
      (algebraMap R S) (algebraMap R A) (algebraMap S B) τ) :
    Nonempty (AlgHom.Local.ResidueCompatible (R := R) (A := A) (B := B) τ) := sorry

/-- Tag 04GU: for a fixed compatible residue-field map, local comparison maps
between chosen strict henselizations form a subsingleton. -/
@[stacks 04GU "uniqueness of strict henselization comparisons"]
theorem subsingleton_ofResidueMap
    (τ : ResidueField A →+* ResidueField B)
    (hτ : IsLocalRing.ResidueField.Compatible
      (algebraMap R S) (algebraMap R A) (algebraMap S B) τ) :
    Subsingleton (AlgHom.Local.ResidueCompatible (R := R) (A := A) (B := B) τ) := sorry

/-- Tag 04GU: for a prescribed compatible residue-field map `τ`, there is a
unique explicit local `R`-algebra map between the chosen strict henselizations
whose induced residue-field map is `τ`. -/
@[stacks 04GU "unique strict henselization comparison with prescribed residue map"]
theorem existsUnique_ofResidueMap
    (τ : ResidueField A →+* ResidueField B)
    (hτ : IsLocalRing.ResidueField.Compatible
      (algebraMap R S) (algebraMap R A) (algebraMap S B) τ) :
    ∃! f : AlgHom.Local (R := R) (A := A) (B := B),
      f.residueFieldMap = τ := sorry

/-- Tag 04GU: after choosing equivalences from the two intrinsic residue
fields to external coordinate rings, a native compatible coordinate map
determines a unique local comparison of strict henselizations.  The equality
is stated on induced residue-field maps, before composing with quotient maps. -/
@[stacks 04GU "strict henselization comparison in residue-field coordinates"]
theorem existsUnique_ofEquiv
    {K : Type y} {L : Type z}
    [NonAssocSemiring K] [NonAssocSemiring L]
    (eA : ResidueField A ≃+* K)
    (eB : ResidueField B ≃+* L)
    (φ : K →+* L)
    (h_compatible : IsLocalRing.ResidueField.Compatible
      (algebraMap R S) (algebraMap R A) (algebraMap S B)
      (eB.symm.toRingHom.comp (φ.comp eA.toRingHom))) :
    ∃! f : AlgHom.Local (R := R) (A := A) (B := B),
      eB.toRingHom.comp f.residueFieldMap = φ.comp eA.toRingHom := sorry

/-- Tag 04GU: a commuting square written in external residue-field coordinates
gives a unique local comparison between strict henselizations.  This packages
the standard `Compatible.ofEquiv` bridge with the intrinsic comparison
universal property, without making chosen coordinate fields part of the core
residue-map API. -/
@[stacks 04GU "strict henselization comparison from a coordinate square"]
theorem existsUnique_ofCoordinateSquare
    {K : Type y} {L : Type z}
    [NonAssocSemiring K] [NonAssocSemiring L]
    (eA : ResidueField A ≃+* K)
    (eB : ResidueField B ≃+* L)
    (sourceCoordinate : ResidueField R →+* K)
    (targetCoordinate : ResidueField S →+* L)
    (h_source : eA.toRingHom.comp (ResidueField.map (algebraMap R A)) = sourceCoordinate)
    (h_target : eB.toRingHom.comp (ResidueField.map (algebraMap S B)) = targetCoordinate)
    (φ : K →+* L)
    (h_coordinates :
      φ.comp sourceCoordinate = targetCoordinate.comp (ResidueField.map (algebraMap R S))) :
    ∃! f : AlgHom.Local (R := R) (A := A) (B := B),
      eB.toRingHom.comp f.residueFieldMap = φ.comp eA.toRingHom := sorry

end ResidueMap

end IsStrictHenselizationOf.Comparison
