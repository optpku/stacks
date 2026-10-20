module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.SeparatedQuasiFinite
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Etale

universe u

/- Lemma 63.3.17 (1): For a separated locally quasi-finite morphism, the stalk
of direct image with proper support is functorially the direct sum of stalks
over same-field geometric lifts. -/
@[stacks 0F57] #check
  (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekStalkIso :
    {X Y : Scheme.{u}} → (f : X ⟶ Y) → [IsSeparated f] →
      [LocallyQuasiFinite f] → [LocallyOfFiniteType f] → (ybar : GeometricPoint Y) →
      etaleLowerShriek f ⋙ (toSmallEtalePoint ybar).sheafFiber ≅
        abelianStalkCoproduct f ybar)

/- Lemma 63.3.17 (2): Direct image with proper support along a separated locally
quasi-finite morphism is exact. -/
@[stacks 0F57] #check
  (AlgebraicGeometry.Scheme.Etale.etaleLowerShriek_exact :
    {X Y : Scheme.{u}} → (f : X ⟶ Y) → [IsSeparated f] →
      [LocallyQuasiFinite f] → [LocallyOfFiniteType f] →
      exactFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (etaleLowerShriek f))
