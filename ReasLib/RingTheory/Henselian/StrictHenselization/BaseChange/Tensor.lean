module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.Henselization.Comparison
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.RingHom.Local.Map
public import ReasLib.RingTheory.RingHom.Local.Residue

@[expose] public section

/-!
# Tensor base change of a strict henselization

This leaf owns the source-independent core of Stacks Lemma 10.155.13.  The
intermediate map is an explicit local algebra homomorphism, so the tensor
product carries the chosen map rather than an ambient, potentially competing
`Algebra` instance.  The residue-field hypothesis is stated as bijectivity of
the canonical map induced by the local base map; a chosen separable closure is
construction data for a downstream comparison, not part of this structural
owner.

@stack 0C2Z
-/

open IsLocalRing
open scoped TensorProduct

universe u v w x y

namespace IsStrictHenselizationOf.BaseChange.Tensor

variable {A : Type u} {B : Type v} {Ah : Type w} {Ash : Type x} {Bh : Type y}
variable [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
variable [Algebra A B] [hAB : IsLocalHom (algebraMap A B)]
variable [CommRing Ah] [Algebra A Ah] [hAh : IsHenselizationOf A Ah]
variable [CommRing Ash] [Algebra Ah Ash]
variable [hAsh : IsStrictHenselizationOf Ah Ash]
variable [CommRing Bh] [Algebra B Bh] [hBh : IsHenselizationOf B Bh]
variable [Algebra A Bh] [hTower : IsScalarTower A B Bh]

/-- The tensor carrier in the strict-henselization base-change construction.
The `Ah`-algebra structure on `Bh` is induced by the supplied local
comparison, and is intentionally scoped to this named carrier. -/
@[stacks 0C2Z "strict henselization base-change tensor carrier"]
noncomputable abbrev carrier
    (comparison : AlgHom.Local (R := A) (A := Ah) (B := Bh)) : Type _ :=
  letI : Algebra Ah Bh := comparison.toAlgebra
  Bh ⊗[Ah] Ash

/-- The explicit `B`-algebra structure on `carrier comparison` induced by the
map `B → Bh`.  It is a definition, rather than an instance, because it
depends on the explicit comparison used to form the tensor carrier. -/
@[stacks 0C2Z "strict henselization base-change tensor algebra"]
noncomputable abbrev algebra
    (comparison : AlgHom.Local (R := A) (A := Ah) (B := Bh)) :
    letI : Algebra Ah Bh := comparison.toAlgebra
    Algebra B (Bh ⊗[Ah] Ash) :=
  letI : Algebra Ah Bh := comparison.toAlgebra
  (Algebra.TensorProduct.includeLeftRingHom (R := Ah) (A := Bh) (B := Ash)).comp
      (algebraMap B Bh) |>.toAlgebra

include hAB hAh hAsh hBh hTower in
/-- The map-level strict-henselization tensor theorem: when the residue-field
map of the explicit local comparison is bijective, its tensor carrier is a
strict henselization of the target base.  This is the fine-grained owner; the
base-map formulation below is a source-facing bridge. -/
@[stacks 0C2Z "strict henselization after residue-field base change"]
theorem isStrict
    (comparison : AlgHom.Local (R := A) (A := Ah) (B := Bh))
    (hκ : Function.Bijective
      comparison.residueFieldMap) :
    letI : Algebra Ah Bh := comparison.toAlgebra
    @IsStrictHenselizationOf B _ _ (Bh ⊗[Ah] Ash) _
      (algebra comparison) := sorry

include hAB hAh hAsh hBh hTower in
/-- The source-level 0C2Z bridge: bijectivity of the residue-field map of the
local base map is enough for the tensor theorem.  The comparison-level form
`isStrict` is the preferred reusable owner when that map is already available.
-/
@[stacks 0C2Z "strict henselization base-map bridge"]
theorem isStrict_of_baseResidueField
    (comparison : AlgHom.Local (R := A) (A := Ah) (B := Bh))
    (hκ : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap A B))) :
    letI : Algebra Ah Bh := comparison.toAlgebra
    @IsStrictHenselizationOf B _ _ (Bh ⊗[Ah] Ash) _
      (algebra comparison) := sorry

end IsStrictHenselizationOf.BaseChange.Tensor
