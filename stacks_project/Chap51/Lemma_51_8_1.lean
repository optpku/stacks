module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.OpenImmersion
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 51.8.1: let `X` be a locally Noetherian scheme, `U` an open subscheme,
and `ℱ` a coherent `𝒪_U`-module. The pushforward of `ℱ` along `U.ι` is coherent
if and only if the same holds for the structure sheaf of the reduced closure of
every `x ∈ associatedPoints ℱ`, first pushed to `U` and then along `U.ι`.
Here `U.ι` represents `j`, `U.compl` represents `Z`, and the reduced point closure
represents `W_x` with its closed immersion `i_x`. -/
@[stacks 0BJZ] #check
  (AlgebraicGeometry.Scheme.Modules.pushforward_obj_isCoherent_iff_associatedPointClosures :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
      (ℱ : (U : Scheme).Modules) [ℱ.IsCoherent],
      (∀ x : U, x ∈ ℱ.associatedPoints →
        ((pushforward U.ι).obj
          (closedSubschemeStructureSheafOn
            (Scheme.PointClosure.reducedStructure x).ideal)).IsCoherent) ↔
        ((pushforward U.ι).obj ℱ).IsCoherent)

end AlgebraicGeometry.Scheme.Modules
