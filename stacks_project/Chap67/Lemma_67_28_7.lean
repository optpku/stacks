module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.Noetherian
import StacksCheckRecall

/-!
# Locally Noetherian targets upgrade finite type to finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.28.7 (1): A morphism of algebraic spaces which is locally of finite
type, with locally Noetherian target, is locally of finite presentation. -/
@[stacks 06G4]
#check (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_of_locallyOfFiniteType :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [IsLocallyNoetherian Y] → [LocallyOfFiniteType f] → LocallyOfFinitePresentation f)

/- Lemma 67.28.7 (2): A morphism of algebraic spaces which is of finite type
and quasi-separated, with locally Noetherian target, is of finite
presentation. -/
@[stacks 06G4]
#check (AlgebraicGeometry.AlgebraicSpace.finitePresentation_of_finiteType :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    [IsLocallyNoetherian Y] → [FiniteType f] → [QuasiSeparated f] → FinitePresentation f)

end AlgebraicGeometry.AlgebraicSpace
