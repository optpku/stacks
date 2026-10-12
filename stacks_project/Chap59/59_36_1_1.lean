/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (𝒢 : Sheaf Y.smallEtaleTopology (Type v))
variable [((smallEtalePullback f).op).HasPointwiseLeftKanExtension 𝒢.1]
variable (U : X.Etale)

/- 59.36.1.1: the value of the small-étale inverse-image presheaf at `U/X`
is the colimit of `𝒢(V/Y)` over arrows `U/X ⟶ X ×_Y V/X`, represented by
the pointwise left Kan extension along `(smallEtalePullback f).op`. -/
@[stacks 04I3] #check
  (AlgebraicGeometry.Scheme.Etale.smallEtaleInverseImagePresheaf_obj f 𝒢 U :
    (Functor.pointwiseLeftKanExtension ((smallEtalePullback f).op) 𝒢.1).obj (op U) =
      colimit (CostructuredArrow.proj ((smallEtalePullback f).op) (op U) ⋙ 𝒢.1))

end AlgebraicGeometry.Scheme
