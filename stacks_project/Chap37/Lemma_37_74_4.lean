/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.UniversallyOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Limit
namespace QcqsMorphismBaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {D : OrderDual I ⥤ Scheme.{u}} {i0 : I} {X0 Y0 : Scheme.{u}}
variable [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
variable [CompactSpace X0] [QuasiSeparatedSpace X0]
variable [CompactSpace Y0] [QuasiSeparatedSpace Y0]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/- Lemma 37.74.4: if the limit base change of a locally finitely presented morphism is
locally quasi-finite and universally open, then both properties hold at one common stage
above the distinguished stage. -/
@[stacks 0F34] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.exists_locallyQuasiFinite_universallyOpen_stage_of_limitHom :
    ∀ (s : QcqsMorphismBaseChange D i0 X0 Y0),
      LocallyQuasiFinite s.limitHom → UniversallyOpen s.limitHom →
        LocallyOfFinitePresentation s.hom →
          ∃ (i : I) (hi0i : i0 ≤ i),
            LocallyQuasiFinite (s.stageHom i hi0i) ∧ UniversallyOpen (s.stageHom i hi0i))

end QcqsMorphismBaseChange
end Limit
end Scheme
end AlgebraicGeometry
