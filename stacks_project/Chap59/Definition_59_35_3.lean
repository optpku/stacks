/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
import StacksCheckRecall

open CategoryTheory
open Opposite
open AlgebraicGeometry

universe u v

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (F : Sheaf X.smallEtaleTopology (Type v))
variable (V : Y.Etale)

/- Definition 59.35.3 (1): the small étale direct image of a sheaf is the
continuous sheaf pushforward along the canonical small étale pullback. -/
@[stacks 03PY] #check
  (AlgebraicGeometry.Scheme.smallEtaleDirectImage f :
    Sheaf X.smallEtaleTopology (Type v) ⥤ Sheaf Y.smallEtaleTopology (Type v))

/- Definition 59.35.3 (2): objectwise, the direct image evaluates the original
sheaf at the base-changed étale object. -/
@[stacks 03PY] #check
  (CategoryTheory.Functor.sheafPushforwardContinuousObjObjIso
    (AlgebraicGeometry.Scheme.smallEtalePullback f) (Type v) F V :
    ((AlgebraicGeometry.Scheme.smallEtaleDirectImage f).obj F).obj.obj (op V) ≅
      F.obj.obj (op ((Scheme.smallEtalePullback f).obj V)))
