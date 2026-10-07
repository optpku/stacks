module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normalization

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.53.4: the relative normalization of a quasi-compact and quasi-separated morphism is
initial among its factorizations through an integral morphism. -/
@[stacks 035I] #check
  (AlgebraicGeometry.Scheme.Hom.existsUnique_lift_fromNormalization :
    ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
      (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π], f = g ≫ π →
      ∃! h : f.normalization ⟶ Z,
        f.toNormalization ≫ h = g ∧ h ≫ π = f.fromNormalization)

#check
  (AlgebraicGeometry.Scheme.Hom.toNormalization_fromNormalization :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f],
      f.toNormalization ≫ f.fromNormalization = f)

#check
  (AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f],
      IsIntegralHom f.fromNormalization)

#check
  (AlgebraicGeometry.Scheme.Hom.instIsDominantToNormalization :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f],
      IsDominant f.toNormalization)

#check
  (AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationDesc :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
      {Z : Scheme.{u}} (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π]
      (hf : f = g ≫ π),
      f.toNormalization ≫ f.normalizationDesc g π hf = g)

#check
  (AlgebraicGeometry.Scheme.Hom.normalizationDesc_comp :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
      {Z : Scheme.{u}} (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π]
      (hf : f = g ≫ π),
      f.normalizationDesc g π hf ≫ π = f.fromNormalization)

#check
  (AlgebraicGeometry.Scheme.Hom.instIsIntegralHomNormalizationDesc :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
      {Z : Scheme.{u}} (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π]
      (hf : f = g ≫ π),
      IsIntegralHom (f.normalizationDesc g π hf))

#check
  (AlgebraicGeometry.Scheme.Hom.existsUnique_lift_normalizationDesc :
    ∀ {X Y Z Z' : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
      (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π] (hf : f = g ≫ π)
      (g' : Y ⟶ Z') (π' : Z' ⟶ Z) [IsIntegralHom π'], g = g' ≫ π' →
      ∃! h' : f.normalization ⟶ Z',
        f.toNormalization ≫ h' = g' ∧ h' ≫ π' = f.normalizationDesc g π hf)
