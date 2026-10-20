module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.AbsoluteWeakNormalization
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 38.38.4: for a functorial choice `awn` of absolute weak normalizations,
the rule sending `X ⟶ S` to `Γ(awn.obj X, 𝒪_(awn.obj X))` is a sheaf of rings on
the big `ph` site `(Sch/S)_{ph}`. -/
@[stacks 0EVT] #check (AlgebraicGeometry.AbsoluteWeakNormalization.phStructurePresheaf_isSheaf :
  ∀
    (S : Scheme.{u}) (awn : Scheme.{u} ⥤ Scheme.{u}) (π : awn ⟶ 𝟭 Scheme.{u})
    (hπ : ∀ X, UniversalHomeomorphism (π.app X))
    (hawn : ∀ X, Scheme.AbsolutelyWeaklyNormal (awn.obj X)),
    Presheaf.IsSheaf (Scheme.bigPhSite S)
      (Scheme.Site.structurePresheaf (Over.forget S ⋙ awn)))
