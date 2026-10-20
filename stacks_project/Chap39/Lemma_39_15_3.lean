module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.FpqcIntersection
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
variable [QuasiCompact f] [QuasiSeparated f] [Flat f] [Surjective f]
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable (F : X.Modules) [F.IsQuasicoherent]
variable (G : Y.Modules) [G.IsCoherent]
variable (φ : G ⟶ (Scheme.Modules.pullback f).obj F) [Mono φ]

/- Lemma 39.15.3: for a flat, surjective, quasi-compact and quasi-separated morphism
`f : Y ⟶ X` of locally Noetherian schemes, if `F` is quasi-coherent and `G` is coherent,
then the pullback of the adjunction unit `F ⟶ f_* f^* F` along the pushforward of a
monomorphism `G ⟶ f^* F` is coherent. -/
@[stacks 07TT] #check
  (AlgebraicGeometry.Scheme.Modules.isCoherent_pullbackUnitPushforward f F G φ :
    (Limits.pullback ((pullbackPushforwardAdjunction f).unit.app F)
      ((Scheme.Modules.pushforward f).map φ)).IsCoherent)

end AlgebraicGeometry.Scheme.Modules
