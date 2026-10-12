/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.OpenImmersion
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Remark 51.8.6 (1): the associated-point boundary obstruction is the first source clause. -/
@[stacks 0AWC] #check
  (AlgebraicGeometry.Scheme.Modules.pushforward_obj_not_isCoherent_of_pointClosure_stalk_dim_le_one :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
      (ℱ : (U : Scheme).Modules) [ℱ.IsCoherent]
      (x : U) (hx : x ∈ ℱ.associatedPoints)
      (z : PointClosure.scheme (U.ι x)) (hz : PointClosure.ι (U.ι x) z ∉ U)
      (h_dimension :
        ringKrullDim ((PointClosure.scheme (U.ι x)).presheaf.stalk z) ≤ 1),
    ¬ ((pushforward U.ι).obj ℱ).IsCoherent)

/- Remark 51.8.6 (2): the completed boundary-stalk obstruction is the second source clause; the
nonempty-open hypothesis excludes the zero pushforward from the empty open. -/
@[stacks 0AWC] #check
  (AlgebraicGeometry.Scheme.Modules.pushforward_structureSheaf_not_isCoherent_of_dim_one :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
      (U : X.Opens) [Nonempty U] (z : X) (hz : z ∉ U)
      (h_associated_dimension :
        let Ahat := AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
          (X.presheaf.stalk z)
        ∃ p ∈ associatedPrimesOfModule Ahat Ahat,
          ringKrullDim (Ahat ⧸ p) = 1),
    ¬ ((pushforward U.ι).obj
      (SheafOfModules.unit (U : Scheme).ringCatSheaf)).IsCoherent)

end AlgebraicGeometry.Scheme.Modules
