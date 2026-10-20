/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.KernelPair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmallSheaf
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation

/-!
# Atlas kernel-pair coequalizers

This module records the sheaf morphism, cofork, and relation properties associated to a
representable étale atlas of an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism of small-valued fppf sheaves associated to a map from a scheme to an algebraic
space. -/
def sheafHom {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints) :
    (Scheme.fppfTopology.over S).yoneda.obj U ⟶ toSmallSheaf F :=
  Sheaf.homEquiv.symm f

/-- The underlying presheaf morphism of `sheafHom f` is `f`. -/
theorem sheafHom_hom {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints) :
    (sheafHom f).hom = f := sorry

/-- The two sheafified projections of the kernel pair equalize `sheafHom f`. -/
theorem sheafHom_equalizes {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    (Scheme.fppfTopology.over S).yoneda.map (kernelPair f h_etale.rep).t ≫ sheafHom f =
      (Scheme.fppfTopology.over S).yoneda.map (kernelPair f h_etale.rep).s ≫
        sheafHom f := sorry

/-- The diagram `R ⇉ U ⟶ F` in the category of small-valued fppf sheaves on `Sch/S`. -/
def cofork {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    Cofork ((Scheme.fppfTopology.over S).yoneda.map (kernelPair f h_etale.rep).t)
      ((Scheme.fppfTopology.over S).yoneda.map (kernelPair f h_etale.rep).s) :=
  Cofork.ofπ (sheafHom f) (sheafHom_equalizes f h_etale)

/-- The coequalizer candidate of `cofork f h_etale` is `sheafHom f`. -/
theorem cofork_π {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    (cofork f h_etale).π = sheafHom f := sorry

/-- An étale-locally surjective atlas remains locally surjective as a morphism of fppf sheaves. -/
instance instIsLocallySurjective_sheafHom {S : Scheme.{u}} {F : AlgebraicSpace S}
    {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    [h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f] :
    Sheaf.IsLocallySurjective (sheafHom f) := sorry

/-- The kernel pair of a representable étale atlas is an internal equivalence relation. -/
instance isEquivalenceRelation {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    IsEquivalenceRelation (kernelPair f h_etale.rep).t (kernelPair f h_etale.rep).s :=
  sorry

/-- The two projections of the kernel pair of a representable étale atlas are étale. -/
theorem etale_projections {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    Etale (kernelPair f h_etale.rep).t.left ∧ Etale (kernelPair f h_etale.rep).s.left :=
  sorry

/-- The first projection of the kernel pair of a representable étale atlas is étale. -/
instance instEtale_kernelPair_t {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    Etale (kernelPair f h_etale.rep).t.left := sorry

/-- The second projection of the kernel pair of a representable étale atlas is étale. -/
instance instEtale_kernelPair_s {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    Etale (kernelPair f h_etale.rep).s.left := sorry

/-- The kernel pair of a representable étale atlas is an étale equivalence relation. -/
instance instIsEtaleEquivalenceRelation_kernelPair {S : Scheme.{u}} {F : AlgebraicSpace S}
    {U : Over S} (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    (kernelPair f h_etale.rep).IsEtaleEquivalenceRelation := sorry

/-- The atlas cofork is a coequalizer in the category of small-valued fppf sheaves. -/
theorem isCoequalizer {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f) :
    Nonempty (IsColimit (cofork f h_etale)) := sorry

end AlgebraicGeometry.AlgebraicSpace
