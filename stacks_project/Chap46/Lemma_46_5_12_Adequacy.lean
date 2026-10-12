/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.UniverseLift

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u v

namespace ModuleValuedFunctor

/- The lifted tensor-extension construction is available from the reusable adequacy API. -/
#check ModuleValuedFunctor.tensorExtensionLifted

/- The objectwise lifted tensor-extension computation is available from the reusable adequacy API. -/
#check ModuleValuedFunctor.tensorExtensionLifted_obj_obj

/- The underlying lifted tensor-extension construction is available from the reusable adequacy API. -/
#check ModuleValuedFunctor.tensorExtensionUnderlyingLifted

/- The underlying lifted tensor-extension computation is available from the reusable adequacy API. -/
#check ModuleValuedFunctor.tensorExtensionUnderlyingLifted_obj

end ModuleValuedFunctor

namespace SheafOfModules

variable {S : Scheme.{u}} {τ : StandardTopology}

/- Lifted affine evaluation is available from the reusable adequacy API. -/
#check SheafOfModules.affineEvaluationLifted

/- The objectwise lifted affine-evaluation computation is available from the reusable adequacy API. -/
#check SheafOfModules.affineEvaluationLifted_obj

/- The underlying lifted affine evaluation is available from the reusable adequacy API. -/
#check SheafOfModules.affineEvaluationUnderlyingLifted

/- The lifted affine-evaluation transport theorem is available from the reusable adequacy API. -/
#check SheafOfModules.affineEvaluationUnderlyingLifted_eq

/- Universe-polymorphic adequacy is available from the reusable adequacy API. -/
#check SheafOfModules.IsAdequateWith

/- The affine-cover characterization of universe-polymorphic adequacy is available from the reusable API. -/
#check SheafOfModules.isAdequateWith_iff

/- The equal-universe adequacy bridge is available from the reusable adequacy API. -/
#check SheafOfModules.isAdequateWith_iff_isAdequate

end SheafOfModules
