module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Map
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Torsion
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Derived étale pushforward along a quasi-compact, quasi-separated morphism
of schemes over a field commutes with extension of that field for bounded-below
complexes whose cohomology stalks are torsion of orders invertible in the field. -/
theorem derivedBaseChange_isIso_of_fieldExtension
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {T S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    (E : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn.{u, u + 1} (Spec (CommRingCat.of K)) :
        ObjectProperty (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) E) :
    IsIso (BaseChange.derivedMapOfCommSq g (FieldExtension.toSource K L s)
      (FieldExtension.baseChangeHom K L s g)
      (FieldExtension.toSource K L (g ≫ s))
      (FieldExtension.baseChangeHom_isPullback K L s g).toCommSq
      (DerivedCategory.Plus.ι.obj E)) := sorry

/-- The canonical derived étale comparison along a field extension is an
isomorphism when the invertible-order torsion condition on bounded-below
cohomology is supplied by `Fact`. -/
instance derivedBaseChange_isIso_of_fieldExtension_of_fact
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {T S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    (E : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    [hE : Fact (DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn.{u, u + 1} (Spec (CommRingCat.of K)) :
        ObjectProperty (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) E)] :
    IsIso (BaseChange.derivedMapOfCommSq g (FieldExtension.toSource K L s)
      (FieldExtension.baseChangeHom K L s g)
      (FieldExtension.toSource K L (g ≫ s))
      (FieldExtension.baseChangeHom_isPullback K L s g).toCommSq
      (DerivedCategory.Plus.ι.obj E)) :=
  derivedBaseChange_isIso_of_fieldExtension s g E hE.out

end AlgebraicGeometry.Scheme.Hom

end
