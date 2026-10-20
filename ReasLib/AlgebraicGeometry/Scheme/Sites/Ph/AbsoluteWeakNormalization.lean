module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Seminormalization
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf

/-!
# Absolute weak normalization on the `ph` site

This module records the sheaf property of global sections after a functorial
choice of absolute weak normalization.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AbsoluteWeakNormalization

/-- For a functorial choice `awn` of absolute weak normalizations, the rule sending
`X ⟶ S` to `Γ(awn.obj X, 𝒪_(awn.obj X))` is a sheaf of rings on the big `ph` site. -/
theorem phStructurePresheaf_isSheaf
    (S : Scheme.{u}) (awn : Scheme.{u} ⥤ Scheme.{u}) (π : awn ⟶ 𝟭 Scheme.{u})
    (hπ : ∀ X, UniversalHomeomorphism (π.app X))
    (hawn : ∀ X, Scheme.AbsolutelyWeaklyNormal (awn.obj X)) :
    Presheaf.IsSheaf (Scheme.bigPhSite S)
      (Scheme.Site.structurePresheaf (Over.forget S ⋙ awn)) := sorry

end AlgebraicGeometry.AbsoluteWeakNormalization
