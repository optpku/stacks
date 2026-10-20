module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.AbsoluteWeakNormalization
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed
public import ReasLib.CategoryTheory.Sites.Sheafification.Map

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.AbsoluteWeakNormalization

/-- The global-sections map induced by a functorial absolute weak normalization presents
`X ↦ Γ(awn.obj X, 𝒪)` as the sheafification of the structure presheaf on a chosen big h
site over `S`. -/
theorem hSheafification
    (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
    (awn : Scheme.{u} ⥤ Scheme.{u}) (π : awn ⟶ 𝟭 Scheme.{u})
    (hπ : ∀ X, UniversalHomeomorphism (π.app X))
    (hawn : ∀ X, Scheme.AbsolutelyWeaklyNormal (awn.obj X)) :
    Presheaf.IsSheafification (ChosenBigHSite.bigTopology Schh S)
      (Scheme.Site.structurePresheafMap (ChosenBigSite.sliceToScheme Schh S) awn
        (ChosenBigSite.sliceToScheme Schh S)
        (Functor.whiskerLeft (ChosenBigSite.sliceToScheme Schh S) π ≫
          (Functor.rightUnitor (ChosenBigSite.sliceToScheme Schh S)).hom)) := sorry

/-- The global-sections map induced by a functorial absolute weak normalization presents
`X ↦ Γ(awn.obj X, 𝒪)` as the sheafification of the structure presheaf for the big ph
topology over `S`. -/
theorem phSheafification
    (S : Scheme.{u}) (awn : Scheme.{u} ⥤ Scheme.{u}) (π : awn ⟶ 𝟭 Scheme.{u})
    (hπ : ∀ X, UniversalHomeomorphism (π.app X))
    (hawn : ∀ X, Scheme.AbsolutelyWeaklyNormal (awn.obj X)) :
    Presheaf.IsSheafification (Scheme.bigPhSite S)
      (Scheme.Site.structurePresheafMap (Over.forget S) awn (Over.forget S)
        (Functor.whiskerLeft (Over.forget S) π ≫
          (Functor.rightUnitor (Over.forget S)).hom)) := sorry

end AlgebraicGeometry.AbsoluteWeakNormalization
