module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

@[expose] public section

/-!
# Prime-localization scalars from a tensor prime

A prime of `B ⊗[A] C` lying over primes of `B` and `C` determines the missing
relative scalar map from `A` localized at its contracted prime to `C`
localized at its induced prime.  This construction is independent of strict
henselizations and is kept as a named non-instance algebra owner to avoid
localization scalar diamonds.  The same diagram also has a scoped contextual
owner for the compatible scalar structures on arbitrary targets over the
three localized rings.

@stack 0GIP
-/

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w y z t

namespace Localization.AtPrime.TensorProduct

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]
variable (pA : Ideal A) [pA.IsPrime]
variable (pB : Ideal B) [pB.IsPrime] [pB.LiesOver pA]
variable (pC : Ideal C) [pC.IsPrime]
variable (pD : Ideal (B ⊗[A] C)) [pD.IsPrime]
variable [pD.LiesOver pB] [pD.LiesOver pC]

include pB pD in
/-- The tensor prime lies over the source prime through its left factor.  This
is a theorem rather than a global instance because the tensor prime is not
determined by the source and target ideals alone. -/
theorem targetLiesOverSource : pD.LiesOver pA :=
  Ideal.LiesOver.trans pD pB pA

include pB pD in
/-- The right prime lies over the source prime through the fixed tensor prime.
This derived relation is exported for statements about the right localization
edge, but is not installed globally. -/
theorem rightLiesOverSource : pC.LiesOver pA := by
  letI : pD.LiesOver pA := targetLiesOverSource pA pB pD
  exact Ideal.LiesOver.tower_bot pD pC pA

include pB pD in
/-- The `Localization.AtPrime pA`-algebra structure on
`Localization.AtPrime pC` determined by a tensor prime `pD`.  The required
relation `pC.LiesOver pA` is derived through `pD`, rather than required as an
extra ambient instance. -/
@[reducible]
noncomputable def algebraOfTensorPrime :
    Algebra (Localization.AtPrime pA) (Localization.AtPrime pC) :=
  -- Local instance justification (proof-local temporary data): derive the two contraction facts
  -- from the fixed tensor prime solely to invoke Mathlib's canonical localization construction.
  letI : pD.LiesOver pA := Ideal.LiesOver.trans pD pB pA
  letI : pC.LiesOver pA := Ideal.LiesOver.tower_bot pD pC pA
  Localization.AtPrime.algebraOfLiesOver pA pC

namespace Edge

/-- The local-ring map from the source localization to the left localization
in a tensor-prime diagram. -/
@[reducible]
noncomputable def sourceLeft :
    Localization.AtPrime pA →+* Localization.AtPrime pB :=
  Localization.localRingHom pA pB (algebraMap A B) (pB.over_def pA)

/-- The source-to-right localization map with its actual minimal hypothesis.
The tensor-prime specialization `sourceRight` below derives this hypothesis
from the surrounding square. -/
@[reducible]
noncomputable def sourceRightOf
    (pA : Ideal A) (pC : Ideal C) [pA.IsPrime] [pC.IsPrime]
    [pC.LiesOver pA] :
    Localization.AtPrime pA →+* Localization.AtPrime pC :=
  Localization.localRingHom pA pC (algebraMap A C) (pC.over_def pA)

/-- The local-ring map from the source localization to the right localization
in a tensor-prime diagram.  The required relation from `pC` to `pA` is derived
through the fixed tensor prime. -/
@[reducible]
noncomputable def sourceRight :
    Localization.AtPrime pA →+* Localization.AtPrime pC :=
  -- Local instance justification (proof-local derived relation): the tensor
  -- prime supplies the contraction of `pC` to `pA` used only for this map.
  letI : pD.LiesOver pA := Ideal.LiesOver.trans pD pB pA
  letI : pC.LiesOver pA := Ideal.LiesOver.tower_bot pD pC pA
  sourceRightOf pA pC

/-- The local-ring map from the left localization to the tensor-prime
localization. -/
@[reducible]
noncomputable def leftTarget :
    Localization.AtPrime pB →+* Localization.AtPrime pD :=
  Localization.localRingHom pB pD
    (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C).toRingHom
    (pD.over_def pB)

/-- The local-ring map from the right localization to the tensor-prime
localization. -/
@[reducible]
noncomputable def rightTarget :
    Localization.AtPrime pC →+* Localization.AtPrime pD :=
  Localization.localRingHom pC pD
    (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom
    (pD.over_def pC)

/-- The direct localization map induced by a tensor-prime ideal lying over a
source prime.  This is the neutral owner of the diagonal edge: unlike the
tensor-prime specialization below, it does not choose a left or right route
through an intermediate localization. -/
@[reducible]
noncomputable def sourceTargetOf
    (pA : Ideal A) (pD : Ideal (B ⊗[A] C)) [pA.IsPrime] [pD.IsPrime]
    [pD.LiesOver pA] :
    Localization.AtPrime pA →+* Localization.AtPrime pD :=
  Localization.localRingHom pA pD (algebraMap A (B ⊗[A] C)) (pD.over_def pA)

/-- The tensor-prime specialization of the neutral direct diagonal owner.
The left and right factorizations are provided separately as bridge theorems,
so consumers do not have to choose a route when naming this map. -/
@[reducible]
noncomputable def sourceTarget :
    Localization.AtPrime pA →+* Localization.AtPrime pD :=
  letI : pD.LiesOver pA := targetLiesOverSource pA pB pD
  sourceTargetOf pA pD

/-- The tensor-prime diagonal is definitionally the neutral direct owner after
installing the contraction supplied by the square. -/
theorem sourceTarget_eq_sourceTargetOf :
    letI : pD.LiesOver pA := targetLiesOverSource pA pB pD
    sourceTarget (pA := pA) (pB := pB) (pD := pD) =
      sourceTargetOf pA pD := sorry

/-- The named source-target edge is the left route in the tensor-prime
localization square. -/
@[simp]
theorem sourceTarget_eq_left :
    sourceTarget (pA := pA) (pB := pB) (pD := pD) =
      (leftTarget (pB := pB) (pD := pD)).comp
        (sourceLeft (pA := pA) (pB := pB)) := sorry

/-- The named source-target edge is also the right route in the tensor-prime
localization square. -/
theorem sourceTarget_eq_right :
    sourceTarget (pA := pA) (pB := pB) (pD := pD) =
      (rightTarget (pC := pC) (pD := pD)).comp
        (sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD)) := sorry

/-- The two localization routes from the source prime to the tensor prime
agree. -/
theorem comm :
    (leftTarget (pB := pB) (pD := pD)).comp
        (sourceLeft (pA := pA) (pB := pB)) =
      (rightTarget (pC := pC) (pD := pD)).comp
        (sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD)) := sorry

end Edge

namespace ResidueField

/-- The residue-field map on the source-to-left edge of a tensor-prime
diagram. -/
noncomputable def sourceLeft :
    pA.ResidueField →+* pB.ResidueField :=
  IsLocalRing.ResidueField.map (Edge.sourceLeft (pA := pA) (pB := pB))

/-- The named source-left residue map is Mathlib's canonical residue-field
map at the corresponding pair of prime ideals. -/
@[simp]
theorem sourceLeft_eq_idealMap :
    sourceLeft (pA := pA) (pB := pB) =
      Ideal.ResidueField.map pA pB (algebraMap A B) (pB.over_def pA) := sorry

/-- The residue-field map on the source-to-right edge of a tensor-prime
diagram. -/
noncomputable def sourceRight :
    pA.ResidueField →+* pC.ResidueField :=
  IsLocalRing.ResidueField.map
    (Edge.sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD))

/-- The named source-right residue map is Mathlib's canonical residue-field
map at the corresponding derived pair of prime ideals. -/
@[simp]
theorem sourceRight_eq_idealMap :
    sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD) =
      letI : pD.LiesOver pA := targetLiesOverSource pA pB pD
      letI : pC.LiesOver pA := rightLiesOverSource pA pB pC pD
      Ideal.ResidueField.map pA pC (algebraMap A C) (pC.over_def pA) := sorry

/-- The residue-field map on the left-to-target edge of a tensor-prime
diagram. -/
noncomputable def leftTarget :
    pB.ResidueField →+* pD.ResidueField :=
  IsLocalRing.ResidueField.map
    (Edge.leftTarget (pB := pB) (pD := pD))

/-- The named left-target residue map is Mathlib's canonical residue-field
map at the corresponding pair of prime ideals. -/
@[simp]
theorem leftTarget_eq_idealMap :
    leftTarget (pB := pB) (pD := pD) =
      Ideal.ResidueField.map pB pD
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C).toRingHom
        (pD.over_def pB) := sorry

/-- The residue-field map on the right-to-target edge of a tensor-prime
diagram. -/
noncomputable def rightTarget :
    pC.ResidueField →+* pD.ResidueField :=
  IsLocalRing.ResidueField.map
    (Edge.rightTarget (pC := pC) (pD := pD))

/-- The named right-target residue map is Mathlib's canonical residue-field
map at the corresponding pair of prime ideals. -/
@[simp]
theorem rightTarget_eq_idealMap :
    rightTarget (pC := pC) (pD := pD) =
      Ideal.ResidueField.map pC pD
        (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom
        (pD.over_def pC) := sorry

/-- The direct residue-field map induced by a tensor-prime ideal lying over a
source prime. -/
noncomputable def sourceTargetOf
    (pA : Ideal A) (pD : Ideal (B ⊗[A] C)) [pA.IsPrime] [pD.IsPrime]
    [pD.LiesOver pA] :
    pA.ResidueField →+* pD.ResidueField :=
  IsLocalRing.ResidueField.map (Edge.sourceTargetOf pA pD)

/-- The direct source-to-target residue map is Mathlib's canonical
residue-field map for the tensor-product algebra map. -/
@[simp]
theorem sourceTargetOf_eq_idealMap
    (pA : Ideal A) (pD : Ideal (B ⊗[A] C)) [pA.IsPrime] [pD.IsPrime]
    [pD.LiesOver pA] :
    sourceTargetOf pA pD =
      Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C)) (pD.over_def pA) := sorry

/-- The residue-field map on the named source-to-target edge of a tensor-prime
diagram. -/
noncomputable def sourceTarget :
    pA.ResidueField →+* pD.ResidueField :=
  letI : pD.LiesOver pA := targetLiesOverSource pA pB pD
  sourceTargetOf pA pD

/-- The tensor-prime source-to-target residue map is the direct owner after
installing the contraction supplied by the square. -/
theorem sourceTarget_eq_sourceTargetOf :
    letI : pD.LiesOver pA := targetLiesOverSource pA pB pD
    sourceTarget (pA := pA) (pB := pB) (pD := pD) =
      sourceTargetOf pA pD := sorry

/-- The named source-target residue map is the left route in the residue-field
square. -/
@[simp]
theorem sourceTarget_eq_left :
    sourceTarget (pA := pA) (pB := pB) (pD := pD) =
      (leftTarget (pB := pB) (pD := pD)).comp
        (sourceLeft (pA := pA) (pB := pB)) := sorry

/-- The named source-target residue map is also the right route in the
residue-field square. -/
theorem sourceTarget_eq_right :
    sourceTarget (pA := pA) (pB := pB) (pD := pD) =
      (rightTarget (pC := pC) (pD := pD)).comp
        (sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD)) := sorry

/-- The two induced residue-field routes from the source prime to the tensor
prime agree. -/
theorem comm :
    (leftTarget (pB := pB) (pD := pD)).comp
        (sourceLeft (pA := pA) (pB := pB)) =
      (rightTarget (pC := pC) (pD := pD)).comp
        (sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD)) := sorry

end ResidueField

namespace Scalars

namespace Edge

/-- The algebra structure on the left localization induced by the named
source-left edge of a tensor-prime diagram.  This is a named owner rather than
a global instance because its tensor-prime parameters are not determined by
the source and left localized rings alone. -/
@[reducible]
noncomputable def sourceLeft :
    Algebra (Localization.AtPrime pA) (Localization.AtPrime pB) :=
  (Localization.AtPrime.TensorProduct.Edge.sourceLeft
    (pA := pA) (pB := pB)).toAlgebra

/-- The source-to-right scalar structure with only the minimal `LiesOver`
hypothesis. -/
@[reducible]
noncomputable def sourceRightOf
    (pA : Ideal A) (pC : Ideal C) [pA.IsPrime] [pC.IsPrime]
    [pC.LiesOver pA] :
    Algebra (Localization.AtPrime pA) (Localization.AtPrime pC) :=
  (Localization.AtPrime.TensorProduct.Edge.sourceRightOf pA pC).toAlgebra

/-- The algebra map of `sourceRightOf` is its underlying direct localization
edge. -/
@[simp]
theorem sourceRightOf_eq
    (pA : Ideal A) (pC : Ideal C) [pA.IsPrime] [pC.IsPrime]
    [pC.LiesOver pA] :
    letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime pC) :=
      sourceRightOf pA pC
    algebraMap (Localization.AtPrime pA) (Localization.AtPrime pC) =
      Localization.AtPrime.TensorProduct.Edge.sourceRightOf pA pC := sorry

/-- The algebra structure on the right localization induced by the named
source-right edge of a tensor-prime diagram. -/
@[reducible]
noncomputable def sourceRight :
    Algebra (Localization.AtPrime pA) (Localization.AtPrime pC) :=
  letI : pD.LiesOver pA := Ideal.LiesOver.trans pD pB pA
  letI : pC.LiesOver pA := Ideal.LiesOver.tower_bot pD pC pA
  sourceRightOf pA pC

/-- The source-to-target scalar structure with only the minimal `LiesOver`
hypothesis. -/
@[reducible]
noncomputable def sourceTargetOf
    (pA : Ideal A) (pD : Ideal (B ⊗[A] C)) [pA.IsPrime] [pD.IsPrime]
    [pD.LiesOver pA] :
    Algebra (Localization.AtPrime pA) (Localization.AtPrime pD) :=
  (Localization.AtPrime.TensorProduct.Edge.sourceTargetOf pA pD).toAlgebra

/-- The algebra map of `sourceTargetOf` is its underlying direct localization
edge. -/
@[simp]
theorem sourceTargetOf_eq
    (pA : Ideal A) (pD : Ideal (B ⊗[A] C)) [pA.IsPrime] [pD.IsPrime]
    [pD.LiesOver pA] :
    letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime pD) :=
      sourceTargetOf pA pD
    algebraMap (Localization.AtPrime pA) (Localization.AtPrime pD) =
      Localization.AtPrime.TensorProduct.Edge.sourceTargetOf pA pD := sorry

/-- The algebra structure on the tensor-prime localization induced by the
named source-target edge. -/
@[reducible]
noncomputable def sourceTarget :
    Algebra (Localization.AtPrime pA) (Localization.AtPrime pD) :=
  letI : pD.LiesOver pA := targetLiesOverSource pA pB pD
  sourceTargetOf pA pD

/-- The algebra structure on the tensor-prime localization induced by the
named left-target edge. -/
@[reducible]
noncomputable def leftTarget :
    Algebra (Localization.AtPrime pB) (Localization.AtPrime pD) :=
  (Localization.AtPrime.TensorProduct.Edge.leftTarget
    (pB := pB) (pD := pD)).toAlgebra

/-- The algebra structure on the tensor-prime localization induced by the
named right-target edge. -/
@[reducible]
noncomputable def rightTarget :
    Algebra (Localization.AtPrime pC) (Localization.AtPrime pD) :=
  (Localization.AtPrime.TensorProduct.Edge.rightTarget
    (pC := pC) (pD := pD)).toAlgebra

/-- The algebra map of the named source-left scalar structure is the
source-left localization edge. -/
@[simp]
theorem sourceLeft_eq :
    letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime pB) :=
      sourceLeft (pA := pA) (pB := pB)
    algebraMap (Localization.AtPrime pA) (Localization.AtPrime pB) =
      Localization.AtPrime.TensorProduct.Edge.sourceLeft
        (pA := pA) (pB := pB) := sorry

/-- The algebra map of the named source-right scalar structure is the
source-right localization edge. -/
@[simp]
theorem sourceRight_eq :
    letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime pC) :=
      sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD)
    algebraMap (Localization.AtPrime pA) (Localization.AtPrime pC) =
      Localization.AtPrime.TensorProduct.Edge.sourceRight
        (pA := pA) (pB := pB) (pC := pC) (pD := pD) := sorry

/-- The algebra map of the named source-target scalar structure is the
source-target localization edge. -/
@[simp]
theorem sourceTarget_eq :
    letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime pD) :=
      sourceTarget (pA := pA) (pB := pB) (pD := pD)
    algebraMap (Localization.AtPrime pA) (Localization.AtPrime pD) =
      Localization.AtPrime.TensorProduct.Edge.sourceTarget
        (pA := pA) (pB := pB) (pD := pD) := sorry

/-- The algebra map of the named left-target scalar structure is the
left-target localization edge. -/
@[simp]
theorem leftTarget_eq :
    letI : Algebra (Localization.AtPrime pB) (Localization.AtPrime pD) :=
      leftTarget (pB := pB) (pD := pD)
    algebraMap (Localization.AtPrime pB) (Localization.AtPrime pD) =
      Localization.AtPrime.TensorProduct.Edge.leftTarget
        (pB := pB) (pD := pD) := sorry

/-- The algebra map of the named right-target scalar structure is the
right-target localization edge. -/
@[simp]
theorem rightTarget_eq :
    letI : Algebra (Localization.AtPrime pC) (Localization.AtPrime pD) :=
      rightTarget (pC := pC) (pD := pD)
    algebraMap (Localization.AtPrime pC) (Localization.AtPrime pD) =
      Localization.AtPrime.TensorProduct.Edge.rightTarget
        (pC := pC) (pD := pD) := sorry

/-- The source-left scalar map between prime localizations is local. -/
theorem sourceLeft_isLocalHom :
    letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime pB) :=
      sourceLeft (pA := pA) (pB := pB)
    IsLocalHom (algebraMap (Localization.AtPrime pA) (Localization.AtPrime pB)) := sorry

/-- The source-right scalar map between prime localizations is local. -/
theorem sourceRight_isLocalHom :
    letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime pC) :=
      sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD)
    IsLocalHom (algebraMap (Localization.AtPrime pA) (Localization.AtPrime pC)) := sorry

/-- The source-target scalar map between prime localizations is local. -/
theorem sourceTarget_isLocalHom :
    letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime pD) :=
      sourceTarget (pA := pA) (pB := pB) (pD := pD)
    IsLocalHom (algebraMap (Localization.AtPrime pA) (Localization.AtPrime pD)) := sorry

/-- The left-target scalar map between prime localizations is local. -/
theorem leftTarget_isLocalHom :
    letI : Algebra (Localization.AtPrime pB) (Localization.AtPrime pD) :=
      leftTarget (pB := pB) (pD := pD)
    IsLocalHom (algebraMap (Localization.AtPrime pB) (Localization.AtPrime pD)) := sorry

/-- The right-target scalar map between prime localizations is local. -/
theorem rightTarget_isLocalHom :
    letI : Algebra (Localization.AtPrime pC) (Localization.AtPrime pD) :=
      rightTarget (pC := pC) (pD := pD)
    IsLocalHom (algebraMap (Localization.AtPrime pC) (Localization.AtPrime pD)) := sorry

end Edge

namespace Target

section

variable {B' : Type y} {C' : Type z} {D' : Type t}
variable [CommRing B'] [CommRing C'] [CommRing D']
variable [Algebra (Localization.AtPrime pB) B']
variable [Algebra (Localization.AtPrime pC) C']
variable [Algebra (Localization.AtPrime pD) D']

/-- The source-localization scalar structure on a left target, constructed
from its given left-localization algebra structure and the source-left edge. -/
@[reducible]
noncomputable def sourceLeft :
    Algebra (Localization.AtPrime pA) B' :=
  ((algebraMap (Localization.AtPrime pB) B').comp
    (Localization.AtPrime.TensorProduct.Edge.sourceLeft
      (pA := pA) (pB := pB))).toAlgebra

/-- The source-to-right scalar structure on an arbitrary target under its
minimal `LiesOver` hypothesis. -/
@[reducible]
noncomputable def sourceRightOf
    (pA : Ideal A) (pC : Ideal C) [pA.IsPrime] [pC.IsPrime]
    [pC.LiesOver pA] [Algebra (Localization.AtPrime pC) C'] :
    Algebra (Localization.AtPrime pA) C' :=
  ((algebraMap (Localization.AtPrime pC) C').comp
    (Localization.AtPrime.TensorProduct.Edge.sourceRightOf pA pC)).toAlgebra

/-- The algebra map of the direct source-to-right target scalar structure is
the displayed composite. -/
@[simp]
theorem sourceRightOf_eq
    (pA : Ideal A) (pC : Ideal C) [pA.IsPrime] [pC.IsPrime]
    [pC.LiesOver pA] [Algebra (Localization.AtPrime pC) C'] :
    letI : Algebra (Localization.AtPrime pA) C' := sourceRightOf (C' := C') pA pC
    algebraMap (Localization.AtPrime pA) C' =
      (algebraMap (Localization.AtPrime pC) C').comp
        (Localization.AtPrime.TensorProduct.Edge.sourceRightOf pA pC) := sorry

/-- The source-localization scalar structure on a right target, constructed
from its given right-localization algebra structure and the source-right edge. -/
@[reducible]
noncomputable def sourceRight :
    Algebra (Localization.AtPrime pA) C' :=
  letI : pD.LiesOver pA := Ideal.LiesOver.trans pD pB pA
  letI : pC.LiesOver pA := Ideal.LiesOver.tower_bot pD pC pA
  sourceRightOf pA pC

/-- The source-to-target scalar structure on an arbitrary target under its
minimal `LiesOver` hypothesis. -/
@[reducible]
noncomputable def sourceTargetOf
    (pA : Ideal A) (pD : Ideal (B ⊗[A] C)) [pA.IsPrime] [pD.IsPrime]
    [pD.LiesOver pA] [Algebra (Localization.AtPrime pD) D'] :
    Algebra (Localization.AtPrime pA) D' :=
  ((algebraMap (Localization.AtPrime pD) D').comp
    (Localization.AtPrime.TensorProduct.Edge.sourceTargetOf pA pD)).toAlgebra

/-- The algebra map of the direct source-to-target target scalar structure is
the displayed composite. -/
@[simp]
theorem sourceTargetOf_eq
    (pA : Ideal A) (pD : Ideal (B ⊗[A] C)) [pA.IsPrime] [pD.IsPrime]
    [pD.LiesOver pA] [Algebra (Localization.AtPrime pD) D'] :
    letI : Algebra (Localization.AtPrime pA) D' := sourceTargetOf (D' := D') pA pD
    algebraMap (Localization.AtPrime pA) D' =
      (algebraMap (Localization.AtPrime pD) D').comp
        (Localization.AtPrime.TensorProduct.Edge.sourceTargetOf pA pD) := sorry

/-- The source-localization scalar structure on a tensor-prime target,
constructed from its given target-localization algebra structure and the
named source-target edge. -/
@[reducible]
noncomputable def sourceTarget :
    Algebra (Localization.AtPrime pA) D' :=
  letI : pD.LiesOver pA := targetLiesOverSource pA pB pD
  sourceTargetOf pA pD

/-- The left-localization scalar structure on a tensor-prime target induced by
the named left-target edge. -/
@[reducible]
noncomputable def leftTarget :
    Algebra (Localization.AtPrime pB) D' :=
  ((algebraMap (Localization.AtPrime pD) D').comp
    (Localization.AtPrime.TensorProduct.Edge.leftTarget
      (pB := pB) (pD := pD))).toAlgebra

/-- The right-localization scalar structure on a tensor-prime target induced
by the named right-target edge. -/
@[reducible]
noncomputable def rightTarget :
    Algebra (Localization.AtPrime pC) D' :=
  ((algebraMap (Localization.AtPrime pD) D').comp
    (Localization.AtPrime.TensorProduct.Edge.rightTarget
      (pC := pC) (pD := pD))).toAlgebra

/-- The source-left target scalar map is the displayed composite through the
named source-left edge. -/
@[simp]
theorem sourceLeft_eq :
    letI : Algebra (Localization.AtPrime pA) B' :=
      sourceLeft (pA := pA) (pB := pB)
    algebraMap (Localization.AtPrime pA) B' =
      (algebraMap (Localization.AtPrime pB) B').comp
        (Localization.AtPrime.TensorProduct.Edge.sourceLeft
          (pA := pA) (pB := pB)) := sorry

/-- The source-right target scalar map is the displayed composite through the
named source-right edge. -/
@[simp]
theorem sourceRight_eq :
    letI : Algebra (Localization.AtPrime pA) C' :=
      sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD)
    algebraMap (Localization.AtPrime pA) C' =
      (algebraMap (Localization.AtPrime pC) C').comp
        (Localization.AtPrime.TensorProduct.Edge.sourceRight
          (pA := pA) (pB := pB) (pC := pC) (pD := pD)) := sorry

/-- The source-target scalar map is the displayed composite through the named
source-target edge. -/
@[simp]
theorem sourceTarget_eq :
    letI : Algebra (Localization.AtPrime pA) D' :=
      sourceTarget (pA := pA) (pB := pB) (pD := pD)
    algebraMap (Localization.AtPrime pA) D' =
      (algebraMap (Localization.AtPrime pD) D').comp
        (Localization.AtPrime.TensorProduct.Edge.sourceTarget
          (pA := pA) (pB := pB) (pD := pD)) := sorry

/-- The left-target scalar map is the displayed composite through the named
left-target edge. -/
@[simp]
theorem leftTarget_eq :
    letI : Algebra (Localization.AtPrime pB) D' :=
      leftTarget (pB := pB) (pD := pD)
    algebraMap (Localization.AtPrime pB) D' =
      (algebraMap (Localization.AtPrime pD) D').comp
        (Localization.AtPrime.TensorProduct.Edge.leftTarget
          (pB := pB) (pD := pD)) := sorry

/-- The right-target scalar map is the displayed composite through the named
right-target edge. -/
@[simp]
theorem rightTarget_eq :
    letI : Algebra (Localization.AtPrime pC) D' :=
      rightTarget (pC := pC) (pD := pD)
    algebraMap (Localization.AtPrime pC) D' =
      (algebraMap (Localization.AtPrime pD) D').comp
        (Localization.AtPrime.TensorProduct.Edge.rightTarget
          (pC := pC) (pD := pD)) := sorry

/-- The named source-left scalar structures form a tower on a left target. -/
theorem sourceLeftTower :
    letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime pB) :=
      Scalars.Edge.sourceLeft (pA := pA) (pB := pB)
    letI : Algebra (Localization.AtPrime pA) B' :=
      sourceLeft (pA := pA) (pB := pB)
    IsScalarTower (Localization.AtPrime pA) (Localization.AtPrime pB) B' := sorry

/-- The named source-right scalar structures form a tower on a right target. -/
theorem sourceRightTower :
    letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime pC) :=
      Scalars.Edge.sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD)
    letI : Algebra (Localization.AtPrime pA) C' :=
      sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD)
    IsScalarTower (Localization.AtPrime pA) (Localization.AtPrime pC) C' := sorry

/-- The named source-left and left-target scalar structures form a tower on a
tensor-prime target. -/
theorem sourceLeftTargetTower :
    letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime pB) :=
      Scalars.Edge.sourceLeft (pA := pA) (pB := pB)
    letI : Algebra (Localization.AtPrime pA) D' :=
      sourceTarget (pA := pA) (pB := pB) (pD := pD)
    letI : Algebra (Localization.AtPrime pB) D' :=
      leftTarget (pB := pB) (pD := pD)
    IsScalarTower (Localization.AtPrime pA) (Localization.AtPrime pB) D' := sorry

/-- The named source-right and right-target scalar structures form a tower on
a tensor-prime target. -/
theorem sourceRightTargetTower :
    letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime pC) :=
      Scalars.Edge.sourceRight (pA := pA) (pB := pB) (pC := pC) (pD := pD)
    letI : Algebra (Localization.AtPrime pA) D' :=
      sourceTarget (pA := pA) (pB := pB) (pD := pD)
    letI : Algebra (Localization.AtPrime pC) D' :=
      rightTarget (pC := pC) (pD := pD)
    IsScalarTower (Localization.AtPrime pA) (Localization.AtPrime pC) D' := sorry

/-- The named left-target scalar structures form a tower from the left
localization to a tensor-prime target. -/
theorem leftTargetTower :
    letI : Algebra (Localization.AtPrime pB) (Localization.AtPrime pD) :=
      Scalars.Edge.leftTarget (pB := pB) (pD := pD)
    letI : Algebra (Localization.AtPrime pB) D' :=
      leftTarget (pB := pB) (pD := pD)
    IsScalarTower (Localization.AtPrime pB) (Localization.AtPrime pD) D' := sorry

/-- The named right-target scalar structures form a tower from the right
localization to a tensor-prime target. -/
theorem rightTargetTower :
    letI : Algebra (Localization.AtPrime pC) (Localization.AtPrime pD) :=
      Scalars.Edge.rightTarget (pC := pC) (pD := pD)
    letI : Algebra (Localization.AtPrime pC) D' :=
      rightTarget (pC := pC) (pD := pD)
    IsScalarTower (Localization.AtPrime pC) (Localization.AtPrime pD) D' := sorry

end

end Target

end Scalars

/-! The neutral diagonal owners are the direct downstream entry points; the
checks below keep their map, residue, and scalar interfaces synchronized. -/

end Localization.AtPrime.TensorProduct
