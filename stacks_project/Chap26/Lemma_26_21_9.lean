module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiSeparated
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y T S : Scheme.{u}} (f : X ⟶ T) (g : Y ⟶ T) (h : T ⟶ S)

/- Lemma 26.21.9 (1): `X ×_T Y ⟶ X ×_S Y` is canonically an immersion. -/
@[stacks 01KR] #check (inferInstance : IsImmersion (pullback.mapDesc f g h))

section

variable [IsSeparated h]

/- Lemma 26.21.9 (2): the comparison is closed when `T ⟶ S` is separated. -/
@[stacks 01KR] #check (inferInstance : IsClosedImmersion (pullback.mapDesc f g h))

end

section

variable [QuasiSeparated h]

/- Lemma 26.21.9 (3): the comparison is quasi-compact when `T ⟶ S` is quasi-separated. -/
@[stacks 01KR] #check pullbackMapDesc_quasiCompact f g h

end
end AlgebraicGeometry
