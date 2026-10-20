module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale.Effectivity.Local

open CategoryTheory CategoryTheory.Limits

universe u v

#check
  (AlgebraicGeometry.Scheme.DescentData.Etale.baseChangeFunctor :
    ∀ {X S T : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S),
      AlgebraicGeometry.Scheme.DescentData.Etale f ⥤
        AlgebraicGeometry.Scheme.DescentData.Etale (pullback.snd f g))

#check
  (AlgebraicGeometry.Scheme.DescentData.Etale.IsEffective.ofOpenCover :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      (D : AlgebraicGeometry.Scheme.DescentData.Etale f)
      {ι : Type v} (U : ι → S.Opens) (hU : TopologicalSpace.IsOpenCover U),
      (∀ i, ((AlgebraicGeometry.Scheme.DescentData.Etale.baseChangeFunctor
          f (U i).ι).obj D).IsEffective) →
        (∀ i j, Nonempty
          (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor
            (pullback.snd f (U i ⊓ U j).ι)).FullyFaithful) →
        (∀ i j k,
          (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor
            (pullback.snd f (U i ⊓ U j ⊓ U k).ι)).Faithful) →
        D.IsEffective)
