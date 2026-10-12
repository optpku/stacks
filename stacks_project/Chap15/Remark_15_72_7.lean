/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat.Iterated
import StacksCheckRecall

/-!
# Coordinates of the abstract iterated Hom comparison

The canonical monoidal construction factors through the same homogeneous coordinate as the
direct construction.  A one-coordinate cochain contributes only on the diagonal, where its
Koszul sign is the direct three-index sign.
-/

@[expose] public section

/-!
# Remark 15.72.7

@stack 0A61
-/

open CategoryTheory.CochainComplex.InternalHom.Module

/- Remark 15.72.7: on the coordinate diagonal, the abstract iterated-Hom comparison is the
signed nested evaluation from the direct construction. -/
@[stacks 0A61 "abstract and direct iterated Hom coordinates agree"]
#check @Iterated.component_tmul_single_apply

#check @Iterated.component_factor
#check @Iterated.component_tmul_single_apply_of_ne
#check @Iterated.coordinate_sign
