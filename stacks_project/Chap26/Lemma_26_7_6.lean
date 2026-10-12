/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}}

/- Lemma 26.7.6: for an affine scheme `Spec R`, kernels and cokernels of quasi-coherent modules
are quasi-coherent.  The reusable owner is intentionally generic in `Scheme.Modules`; these
checks pin the chapter entry to the affine situation of the source. -/
@[stacks 01IC] #check @Scheme.Modules.isQuasicoherent_kernel (Spec R)
#check @Scheme.Modules.isQuasicoherent_cokernel (Spec R)

/- Generic companion API for later non-affine reuse. -/
#check Scheme.Modules.isQuasicoherent_kernel
#check Scheme.Modules.isQuasicoherent_cokernel
