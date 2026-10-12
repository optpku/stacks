/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

variable {R : CommRingCat.{u}}

/- Lemma 26.7.7: on the affine scheme `Spec R`, arbitrary coproducts and, more generally,
colimits of quasi-coherent modules are quasi-coherent. -/
@[stacks 01ID] #check @Scheme.Modules.isQuasicoherent_coproduct (Spec R)
@[stacks 01ID] #check @Scheme.Modules.isQuasicoherent_colimit (Spec R)

section

variable (R : CommRingCat.{u}) {J : Type u} [Category.{u} J]

@[stacks 01ID] #check
  (inferInstance : HasColimitsOfShape J (Scheme.QCoh (Spec R)))
#check
  (inferInstance : PreservesColimitsOfShape J (Scheme.QCoh.inclusion (Spec R)))

end

/- Generic companion owners remain available for arbitrary schemes. -/
#check Scheme.QCoh.closedUnderColimitsOfShape
#check Scheme.Modules.isQuasicoherent_colimit
#check Scheme.Modules.isQuasicoherent_coproduct
