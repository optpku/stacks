module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfSite

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u uC

variable {C : Type uC} [Category.{u} C] (ι : C ⥤ Scheme.{u})
variable (J : GrothendieckTopology C) (X : C)
variable [J.Subcanonical] [ι.Full] [ι.Faithful]
variable [PreservesLimitsOfShape WalkingCospan ι]
variable [(slicePost ι X).IsContinuous (J.over X) (Scheme.fppfTopology.over (ι.obj X))]
variable [HasWeakSheafify (Scheme.fppfTopology.over (ι.obj X)) (Type u)]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type u, (slicePost ι X).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((slicePost ι X).sheafPullback (Type u) (J.over X)
    (Scheme.fppfTopology.over (ι.obj X)))]
variable (F : Sheaf (J.over X) (Type u))
variable (hdiag : yoneda.relativelyRepresentable (Limits.diag F.obj))
variable {U₀ : Over X} (p : yoneda.obj U₀ ⟶ F.obj)
variable (hp : yoneda.relativelyRepresentable p)
variable (hp_etale : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
  (MorphismProperty.over (@Etale)) ((slicePost ι X).map (hp.snd ξ)))
variable (hp_surj : ∀ {V : Over X} (ξ : yoneda.obj V ⟶ F.obj),
  Surjective ((slicePost ι X).map (hp.snd ξ)).left)

/- Lemma 65.15.1: the ambient-scheme specialization constructs the inverse-image
algebraic space from its explicit transported atlas. -/
#check (AlgebraicGeometry.AlgebraicSpace.ofInverseImage
  ι J X F hdiag p hp hp_etale hp_surj : AlgebraicSpace (ι.obj X))
