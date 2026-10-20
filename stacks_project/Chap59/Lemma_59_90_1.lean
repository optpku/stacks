module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.FieldExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

/- Lemma 59.90.1: Derived étale pushforward along a quasi-compact,
quasi-separated morphism of schemes over a field commutes with arbitrary field
extension for bounded-below complexes whose cohomology stalks are torsion of
orders invertible in the field. -/
@[stacks 0F1C] #check
  (AlgebraicGeometry.Scheme.Hom.derivedBaseChange_isIso_of_fieldExtension :
    ∀
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {T S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    (E : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn.{u, u + 1} (Spec (CommRingCat.of K)) :
        ObjectProperty (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) E),
    IsIso (BaseChange.derivedMapOfCommSq g (FieldExtension.toSource K L s)
      (FieldExtension.baseChangeHom K L s g)
      (FieldExtension.toSource K L (g ≫ s))
      (FieldExtension.baseChangeHom_isPullback K L s g).toCommSq
      (DerivedCategory.Plus.ι.obj E)))

end
