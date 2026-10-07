module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import stacks_project.Chap65.Definition_65_9_3_EtaleEquivalence
public import stacks_project.Chap65.Lemma_65_9_1_KernelPair

/-!
# Lemma 65.9.1

A surjective étale morphism from a scheme to an algebraic space has kernel pair an
étale equivalence relation, and is a coequalizer in the category of fppf sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The functor of points of an algebraic space, as an object of the category of fppf sheaves
on `Sch/S`. -/
def toSheaf {S : Scheme.{u}} (F : AlgebraicSpace S) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  ⟨F.functorOfPoints, F.isSheaf⟩

/-- The underlying presheaf of `toSheaf F` is the functor of points of `F`. -/
theorem toSheaf_obj {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (toSheaf F).obj = F.functorOfPoints := sorry

/-- The morphism of fppf sheaves associated to a map from a scheme to an algebraic space. -/
def sheafHom {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints) :
    (Scheme.fppfTopology.over S).yoneda.obj U ⟶ toSheaf F :=
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

/-- The diagram `R ⇉ U ⟶ F` in the category of fppf sheaves on `Sch/S`. -/
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

/-- An étale-locally surjective atlas remains locally surjective as a morphism of fppf
sheaves. -/
theorem isLocallySurjective_sheafHom {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f) :
    Sheaf.IsLocallySurjective (sheafHom f) := sorry

/-- Lemma 65.9.1 (1): `j : R ⟶ U ×_S U` defines an equivalence relation on `U` over `S`. -/
@[stacks 0262]
instance isEquivalenceRelation {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f) :
    IsEquivalenceRelation (kernelPair f h_etale.rep).t (kernelPair f h_etale.rep).s :=
  sorry

/-- Lemma 65.9.1 (2): the projections `s, t : R ⟶ U` are étale. -/
@[stacks 0262]
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

/-- Lemma 65.9.1 (3): `R ⇉ U ⟶ F` is a coequalizer diagram in
`Sheaf ((Sch/S)_fppf)`. -/
@[stacks 0262]
theorem isCoequalizer {S : Scheme.{u}} {F : AlgebraicSpace S} {U : Over S}
    (f : yoneda.obj U ⟶ F.functorOfPoints)
    (h_etale : (MorphismProperty.over (@Etale)).presheaf f)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f) :
    Nonempty (IsColimit (cofork f h_etale)) := sorry

end AlgebraicGeometry.AlgebraicSpace
