module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantDirectImage
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 59.80.5: if `f : X ⟶ Y` is a morphism of schemes and `X` is integral
normal with separably closed function field, then the positive-degree higher direct image of
the constant abelian sheaf vanishes. -/
@[stacks 0EZP]
#check (AlgebraicGeometry.Scheme.higherDirectImage_constantSheaf_isZero :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] (hX : X.isNormal)
      [IsSepClosed X.functionField] (M : AddCommGrpCat.{u}) {q : ℕ} (hq : 0 < q)
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})],
      IsZero
        (Sheaf.higherDirectImage (smallEtalePullback f)
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M) q :
          Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))

end AlgebraicGeometry.Scheme
