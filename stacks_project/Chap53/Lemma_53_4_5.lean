module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve.ClosedImmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/- Lemma 53.4.5 (1) -/
@[stacks 0E33]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.properDualizingComplex_closedImmersion :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      {Y : Scheme.{u}} → (i : Y ⟶ X.left) → [IsClosedImmersion i] →
      topologicalKrullDim X.left ≤ 1 →
      IsIsomorphic (AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex
        (i ≫ X.hom)).obj
        ((AlgebraicGeometry.RingedSpace.ModuleDerived.ClosedImmersion.rHomFromStructureSheaf
          i.toShHom (IsClosedImmersion.isClosedEmbedding i)).obj
          (AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex
            X.hom).obj))

/- Lemma 53.4.5 (2) -/
@[stacks 0E33]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule_closedImmersion :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      {Y : Scheme.{u}} → (i : Y ⟶ X.left) → [IsClosedImmersion i] →
      topologicalKrullDim X.left ≤ 1 →
      IsIsomorphic
        (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule
          (i ≫ X.hom))
        ((AlgebraicGeometry.RingedSpace.Hom.ModulePushforward.ClosedImmersion.homFromStructureSheaf
          i.toShHom (IsClosedImmersion.isClosedEmbedding i)).obj
          (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule
            X.hom)))

/- Lemma 53.4.5 (3) -/
@[stacks 0E33]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.pushforward_curveDualizingModule_closedImmersion :
    {k : Type u} → [Field k] → (X : SchemeOverField k) → [IsProper X.hom] →
      {Y : Scheme.{u}} → (i : Y ⟶ X.left) → [IsClosedImmersion i] →
      topologicalKrullDim X.left ≤ 1 →
      IsIsomorphic
        ((AlgebraicGeometry.RingedSpace.Hom.pushforward i.toShHom).obj
          (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule
            (i ≫ X.hom)))
        ((AlgebraicGeometry.RingedSpace.Hom.ModulePushforward.ClosedImmersion.ambientInternalHom
          i.toShHom).obj
          (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule
            X.hom)))
