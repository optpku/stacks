/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Separable.Generated.OnePthRoot
public import ReasLib.FieldTheory.Separable.Generated.GeometricallyReduced
import StacksCheckRecall

@[expose] public section

/-!
# First Frobenius-root separability criteria

Lemma 10.44.2 (Tag 030W) is a canonical recall block.  The concrete model
`IntermediateField.onePthRootExtension k p` belongs to the purely inseparable
field-extension library, while the independent separability criteria belong to
the `Algebra.IsSeparableOver` namespace.

@stack 030W
-/

/- Lemma 10.44.2 (Tag 030W), first Frobenius-root field. -/
@[stacks 030W]
#check @IntermediateField.onePthRootSubfield
#check @IntermediateField.onePthRootExtension
#check @IntermediateField.mem_onePthRootExtension_iff

/- Lemma 10.44.2 (Tag 030W), Frobenius linear-independence criterion. -/
@[stacks 030W]
#check @Algebra.IsSeparableOver.iff_linearIndepOn_pow
#check @Algebra.IsSeparableOver.OnePthRoot.linearIndepOn_pow
#check @Algebra.IsSeparableOver.OnePthRoot.linearIndepOn_pow_of

/- Lemma 10.44.2 (Tag 030W), reduced first-root base-change criterion. -/
@[stacks 030W]
#check @Algebra.IsSeparableOver.OnePthRoot.iff_isReduced

/- Lemma 10.44.2 (Tag 030W), geometric-reducedness criterion.  The source
   assumptions are retained by the `CharP`-scoped owner; the unrestricted
   theorem is checked separately as a stronger shared companion. -/
@[stacks 030W]
#check @Algebra.IsSeparableOver.CharP.iff_isGeometricallyReduced
#check @Algebra.IsSeparableOver.iff_isGeometricallyReduced
