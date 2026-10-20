/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.RingHom.Local.Map
public import ReasLib.RingTheory.RingHom.Local.Residue

@[expose] public section

/-!
# Lifts from Henselizations

This file owns the universal property of a chosen henselization.  Its target
is an arbitrary henselian local algebra over the base; comparisons between two
chosen henselizations are a specialization.  The API intentionally states
existence and uniqueness without selecting a witness: a `Classical.choose`
definition would make non-Prop comparison data depend on deferred proof debt.
Given explicit local lifts in both directions, `algEquivOfLocal` assembles
them into the comparison equivalence.  `IsHenselizationOf` is propositional and
carries no lift data, so a zero-input comparison remains `nonemptyAlgEquiv`.

@stack 04GS
-/

universe u v w x

namespace IsHenselizationOf

section Lift

variable {R : Type u} {Rh : Type v} {T : Type w}
variable [hCommR : CommRing R] [hLocalR : IsLocalRing R]
variable [hCommRh : CommRing Rh] [hRRh : Algebra R Rh] [hRh : IsHenselizationOf R Rh]
variable [hCommT : CommRing T] [hT : HenselianLocalRing T] [hRT : Algebra R T]
variable [hRTLocal : IsLocalHom (algebraMap R T)]

-- The target's henselian and local algebra structures are mathematical input to these lifts,
-- even though they do not occur syntactically in the conclusion.
include hCommR hLocalR hCommRh hRRh hRh hCommT hT hRT hRTLocal

/-- Tag 04GS: a henselization has a unique local lift to every henselian local
`R`-algebra. -/
@[stacks 04GS "henselization universal property"]
theorem existsUnique_lift :
    ∃! f : Rh →ₐ[R] T, IsLocalHom f.toRingHom := sorry

/-- Tag 04GS: there exists an explicit local algebra map from a henselization
to every henselian local target over its base.  The result stays
proposition-valued, so downstream proofs may choose a comparison locally
without installing a noncanonical global map. -/
@[stacks 04GS "existence of a local henselization lift"]
theorem local_nonempty :
    Nonempty (AlgHom.Local (R := R) (A := Rh) (B := T)) := sorry

/-- Tag 04GS: explicit local algebra maps from a henselization to a fixed
henselian local target form a subsingleton. -/
@[stacks 04GS "uniqueness of henselization lifts"]
theorem local_subsingleton :
    Subsingleton (AlgHom.Local (R := R) (A := Rh) (B := T)) := sorry

/-- Tag 04GS: two explicit local lifts from a henselization to the same
henselian local target are equal. -/
@[stacks 04GS "equality of henselization lifts"]
theorem local_eq (f g : AlgHom.Local (R := R) (A := Rh) (B := T)) : f = g := sorry

omit hCommR hLocalR hCommRh hRRh hRh hCommT hT hRT hRTLocal

end Lift

section Equiv

variable {R : Type u} {Rh : Type v} {Sh : Type w}
variable [hCommR : CommRing R] [hLocalR : IsLocalRing R]
variable [hCommRh : CommRing Rh] [hRRh : Algebra R Rh] [hRh : IsHenselizationOf R Rh]
variable [hCommSh : CommRing Sh] [hRSh : Algebra R Sh] [hSh : IsHenselizationOf R Sh]

-- Both henselization structures are essential to the comparison equivalence.
include hCommR hLocalR hCommRh hRRh hRh hCommSh hRSh hSh

/-- Tag 04GS: any two chosen henselizations of the same local ring are
isomorphic as algebras over that ring.  The result is proposition-valued, so
it does not choose an equivalence as public data. -/
@[stacks 04GS "equivalence of chosen henselizations"]
theorem nonemptyAlgEquiv : Nonempty (Rh ≃ₐ[R] Sh) := sorry

/-- Tag 04GS: explicit local lifts in both directions between two chosen
henselizations are mutually inverse, by uniqueness of local lifts into a
henselization.  The forward and inverse maps are the given lifts. -/
@[stacks 04GS "equivalence of henselizations from explicit local lifts"]
def algEquivOfLocal
    (f : AlgHom.Local (R := R) (A := Rh) (B := Sh))
    (g : AlgHom.Local (R := R) (A := Sh) (B := Rh)) : Rh ≃ₐ[R] Sh :=
  AlgEquiv.ofAlgHom f.hom g.hom
    (congrArg AlgHom.Local.hom
      (local_eq (R := R) (Rh := Sh) (T := Sh) (f.comp g)
        ⟨AlgHom.id R Sh, by change IsLocalHom (RingHom.id Sh); infer_instance⟩))
    (congrArg AlgHom.Local.hom
      (local_eq (R := R) (Rh := Rh) (T := Rh) (g.comp f)
        ⟨AlgHom.id R Rh, by change IsLocalHom (RingHom.id Rh); infer_instance⟩))

/-- The comparison built from explicit local lifts acts by the forward lift. -/
@[simp]
theorem algEquivOfLocal_apply
    (f : AlgHom.Local (R := R) (A := Rh) (B := Sh))
    (g : AlgHom.Local (R := R) (A := Sh) (B := Rh)) (x : Rh) :
    algEquivOfLocal f g x = f.hom x := rfl

/-- The inverse of the comparison built from explicit local lifts is the
backward lift. -/
@[simp]
theorem algEquivOfLocal_symm_apply
    (f : AlgHom.Local (R := R) (A := Rh) (B := Sh))
    (g : AlgHom.Local (R := R) (A := Sh) (B := Rh)) (y : Sh) :
    (algEquivOfLocal f g).symm y = g.hom y := rfl

omit hCommR hLocalR hCommRh hRRh hRh hCommSh hRSh hSh

end Equiv

section ResidueMap

variable {R : Type u} {S : Type v} {Rh : Type w} {Sh : Type x}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [IsLocalRing S]
variable [Algebra R S] [hRSLocal : IsLocalHom (algebraMap R S)]
variable [CommRing Rh] [Algebra R Rh] [hRh : IsHenselizationOf R Rh]
variable [CommRing Sh] [Algebra S Sh] [Algebra R Sh]
variable [hTower : IsScalarTower R S Sh] [hSh : IsHenselizationOf S Sh]

include hRSLocal hRh hSh hTower

/-- Tag 04GS: the residue-field map of a local comparison between chosen
henselizations is forced by the base residue-field map.  The displayed
formula is the neutral replacement for a construction-dependent choice of
separable-closure embeddings. -/
@[stacks 04GS "residue-field map of a henselization comparison"]
theorem residueFieldMap_eq_base
    (f : AlgHom.Local (R := R) (A := Rh) (B := Sh)) :
    f.residueFieldMap =
      (IsHenselizationOf.residueFieldEquiv (R := S) (S := Sh)).toRingHom.comp
        ((IsLocalRing.ResidueField.map (algebraMap R S)).comp
          (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm.toRingHom) := sorry

/-- Tag 04GS: if the base local map induces a bijection on residue fields,
then every local comparison between the corresponding henselizations does so
as well. -/
@[stacks 04GS "bijective residue-field map of a henselization comparison"]
theorem residueFieldMap_bijective_of_base
    (f : AlgHom.Local (R := R) (A := Rh) (B := Sh))
    (hκ : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R S))) :
    Function.Bijective f.residueFieldMap := sorry

end ResidueMap

end IsHenselizationOf
